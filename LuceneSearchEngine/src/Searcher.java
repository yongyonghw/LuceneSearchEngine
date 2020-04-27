package com.giosis.qube.extend.search;

import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

import org.apache.lucene.index.LeafReader;
import org.terracotta.context.query.Queries;

import com.giosis.qube.config.QDBConfigHandler;
import com.giosis.qube.config.QDBModel;
import com.giosis.qube.config.ServerConfigHandler;
import com.giosis.qube.config.ServerConfigHandler.ServerType;
import com.giosis.qube.config.qdb.Dimension;
import com.giosis.qube.config.qdb.Facetconfig;
import com.giosis.qube.config.qdb.Fieldconfig;
import com.giosis.qube.config.qdb.Facetconfig.Facet;
import com.giosis.qube.config.qdb.Fieldconfig.Field;
import com.giosis.qube.constants.QDBConst;
import com.giosis.qube.constants.QDBConst.QDBCacheType;
import com.giosis.qube.constants.QueryConst;
import com.giosis.qube.core.QubeCore;
import com.giosis.qube.core.document.Document;
import com.giosis.qube.core.facet.FacetResult;
import com.giosis.qube.core.facet.Facets;
import com.giosis.qube.core.facet.FacetsCollector;
import com.giosis.qube.core.facet.FacetsConfig;
import com.giosis.qube.core.facet.taxonomy.directory.DirectoryTaxonomyReader;
import com.giosis.qube.core.index.DirectoryReader;
import com.giosis.qube.core.index.DocValuesType;
import com.giosis.qube.core.index.FieldInfo;
import com.giosis.qube.core.index.FieldInfos;
import com.giosis.qube.core.index.LeafReaderContext;
import com.giosis.qube.core.search.BooleanClause.Occur;
import com.giosis.qube.core.search.BooleanQuery;
import com.giosis.qube.core.search.CollectionStatistics;
import com.giosis.qube.core.search.Collector;
import com.giosis.qube.core.search.FieldDoc;
import com.giosis.qube.core.search.IndexSearcher;
import com.giosis.qube.core.search.MatchNoDocsQuery;
import com.giosis.qube.core.search.Query;
import com.giosis.qube.core.search.ScoreDoc;
import com.giosis.qube.core.search.Sort;
import com.giosis.qube.core.search.SortField;
import com.giosis.qube.core.search.TimeLimitingCollector;
import com.giosis.qube.core.search.TopDocs;
import com.giosis.qube.core.search.TopDocsCollector;
import com.giosis.qube.core.search.TopFieldCollector;
import com.giosis.qube.core.search.TopScoreDocCollector;
import com.giosis.qube.exception.QError;
import com.giosis.qube.exception.QException;
import com.giosis.qube.extend.facet.FacetMath;
import com.giosis.qube.extend.facet.FacetNode;
import com.giosis.qube.extend.facet.FacetResultCache;
import com.giosis.qube.extend.facet.FacetResultPerType;
import com.giosis.qube.extend.facet.QubeFacetResult;
import com.giosis.qube.extend.facet.QubeLabelAndValue;
import com.giosis.qube.extend.facet.QubeSortedSetDocValuesReaderState;
import com.giosis.qube.extend.facet.QubeSortedSetFacet;
import com.giosis.qube.extend.facet.QubeTaxonomyFacet;
import com.giosis.qube.extend.facet.FacetMath.FacetMathType;
import com.giosis.qube.extend.facet.FacetMathSort;
import com.giosis.qube.img.ImageSortComparator;
import com.giosis.qube.img.ImgUtil;
import com.giosis.qube.img.QubeImageBulider;
import com.giosis.qube.lire.utils.ImageUtils;
import com.giosis.qube.extend.query.WarmUpQuery;
import com.giosis.qube.logger.LoggerEngine;
import com.giosis.qube.query.extend.FacetCollate;
import com.giosis.qube.query.extend.Parser;
import com.giosis.qube.query.extend.QueryContainer;
import com.giosis.qube.query.extend.Synonym;
import com.giosis.qube.util.LRUCache;
import com.giosis.qube.util.ObjectCopy;
import com.giosis.qube.util.Tool;

/**
 * Qube �˻��� - �ؽ�Ʈ, ���̳ʸ�, �̹���, Facet, Join 
 * @since Qube2.0
 * @author jilee - Lucene6.3.0������� ���� 2016-12-26
 *
 */
public class QubeSearcher extends QubeCore{
	private final String qdb;
	private final String indexDir;
	/**
	 * �پ��� ����� ���� wrapping �� reader 
	 */
	private DirectoryReader reader;
	/**
	 * reader�� �̿��� �۾��� reader wrapping���� ���� Overhead ������ ���� �� Reader�� �޾Ƽ� ����Ѵ�.
	 */
	private DirectoryReader rawReader; 
	/**
	 * Core Searcher
	 */
	private IndexSearcher searcher;
	/**
	 * Facet Search�� ���� TaxonomyReader
	 */
	private DirectoryTaxonomyReader taxoReader;
	private FacetsConfig fConfig;
	
	protected final LRUCache<QueryResultKey,DocListAndSet> queryResultCache = new LRUCache<QueryResultKey, DocListAndSet>();
	protected final LRUCache<Integer,Document> documentCache = new LRUCache<Integer, Document>();
	/**
	 * Facet��� ĳ�� �߰� by jilee 2017-09-04
	 * QueryResultCache������ �����ϰ� �����Ѵ�.
	 */
	//protected final LRUCache<FacetResultKey, List<List<QubeFacetResult>>> facetCache = new LRUCache<FacetResultKey, List<List<QubeFacetResult>>>();
	protected final LRUCache<FacetResultKey, FacetResultCache> facetCache = new LRUCache<FacetResultKey, FacetResultCache>();
	/**
	 * 2018-07-03 SSDV Cach �߰� 2018-07-03 by ktKim
	 * * ���� : ��� FacetConfig�� ������ �ʵ��� QubeSortedSetDocValuesReaderState�� �ε� �ð��� �ټ� �ҿ� �ǹǷ� Searcher ������ �̸� ĳ���Ѵ�.
	 */
	protected final ConcurrentHashMap<String, QubeSortedSetDocValuesReaderState> ssdvStateCache = new ConcurrentHashMap<String, QubeSortedSetDocValuesReaderState>();
	
	private List<WarmUpQuery> warmupQueries=null;
	
	/**
	 * �̹��� �˻�
	 */
	private ImageSortComparator comparator = null;
	/**
	 * QubeSearch ������ �� �̹��� ĳ�ø� �������� ����
	 */
	private boolean useNewImgCache = true;
	private int warmupSize;
	
	/**
	 * 2018-08-30 Searcher Close�� ���� ���� �߰� by ktKim
	 * currentSearchCnt = ���� Searcher���� �˻��ϰ� �ִ� Count
	 * totalSearchCnt = Searcher�� ������ SearchUnit�� ���� �� �˻���û�� �� Count
	 */
//	private volatile int currentSearchCnt;
	private AtomicLong totalSearchCnt = new AtomicLong(0);
	private AtomicInteger currentSearchCnt = new AtomicInteger(0);
	
	public static final String WARMUP_FILENAME="warm-up-query.txt";
	
	//Executor 
	private ExecutorService executor = null;
	
	/**
	 * QDB.xml �� �ƴ� reader�� ���� �߰��� �ʵ�����
	 * ����� Json���� ��� by yonghw 20200212 
	 */
	//Json ������ Ű�� �����ϴ�, ��� Json �ʵ���� ������� �÷��ָ�
	private Map<String, Fieldconfig.Field> dynamicFieldConfig = new HashMap<>();
	
	public QubeSearcher(String qdb, boolean useNewImgCache, DirectoryReader refreshReader, DirectoryTaxonomyReader refreshTaxoReader) {
		// TODO Auto-generated constructor stub
		boolean isSearcherCreate = false;
		//2017-11-16 facetReaderCreate by ktKim
		boolean isTaxonomyReaderCreate = false;
		this.qdb = qdb;
		this.indexDir = QDBConfigHandler.getInstance().getIndexDir(qdb);
		QDBModel model = QDBConfigHandler.getInstance().getConfig(qdb);
		
		//warmup size ����
		this.warmupSize = model.getQdbConfig().getWarmupSize();
		
		int qrInit=0, qrLimit=0;
		int docInit=0, docLimit=0;
		int facetDocInit=0, facetDocLimit=0;
		
		//Cacheconfig qdbCacheConfig = model.getCacheConfig();
		//QDB Config�� ���� �������� ���� �� ServerCnfig�� Cache�� ����ϵ��� ����
		if(QubeCore.getQDBConfigCache(qdb, QDBCacheType.QUERY_RESULT_CACHE.getValue()) != null) {
			qrInit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.QUERY_RESULT_CACHE.getValue()).getInitSize();
			qrLimit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.QUERY_RESULT_CACHE.getValue()).getLimitSize();
		}else if(QubeCore.getServerConfigCache(QDBCacheType.QUERY_RESULT_CACHE.getValue()) != null){
			qrInit = QubeCore.getServerConfigCache(QDBCacheType.QUERY_RESULT_CACHE.getValue()).getInitSize();
			qrLimit = QubeCore.getServerConfigCache(QDBCacheType.QUERY_RESULT_CACHE.getValue()).getLimitSize();
		}else {
			new QException(QError.SEARCHER_CREATE_FAIL, QError.SEARCHER_CREATE_FAIL_MSG,QDBCacheType.QUERY_RESULT_CACHE.getValue()+" Not Exist.").logError();
		}
		
		if(QubeCore.getQDBConfigCache(qdb, QDBCacheType.DOCUMENT_CACHE.getValue()) != null) {
			docInit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.DOCUMENT_CACHE.getValue()).getInitSize();
			docLimit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.DOCUMENT_CACHE.getValue()).getLimitSize();
		}else if(QubeCore.getServerConfigCache(QDBCacheType.DOCUMENT_CACHE.getValue()) != null){
			docInit = QubeCore.getServerConfigCache(QDBCacheType.DOCUMENT_CACHE.getValue()).getInitSize();
			docLimit = QubeCore.getServerConfigCache(QDBCacheType.DOCUMENT_CACHE.getValue()).getLimitSize();
		}else {
			new QException(QError.SEARCHER_CREATE_FAIL, QError.SEARCHER_CREATE_FAIL_MSG,QDBCacheType.DOCUMENT_CACHE.getValue()+" Not Exist.").logError();
		}
		
		if(QubeCore.getQDBConfigCache(qdb, QDBCacheType.FACET_CACHE.getValue()) != null) {
			facetDocInit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.FACET_CACHE.getValue()).getInitSize();
			facetDocLimit = QubeCore.getQDBConfigCache(qdb, QDBCacheType.FACET_CACHE.getValue()).getLimitSize();
		}else if(QubeCore.getServerConfigCache(QDBCacheType.FACET_CACHE.getValue()) != null){
			facetDocInit = QubeCore.getServerConfigCache(QDBCacheType.FACET_CACHE.getValue()).getInitSize();
			facetDocLimit = QubeCore.getServerConfigCache(QDBCacheType.FACET_CACHE.getValue()).getLimitSize();
		}else {
			new QException(QError.SEARCHER_CREATE_FAIL, QError.SEARCHER_CREATE_FAIL_MSG,QDBCacheType.FACET_CACHE.getValue()+" Not Exist.").logError();
		}
		
		queryResultCache.init("queryResultCache" ,qrInit ,qrLimit);
		queryResultCache.setState(LRUCache.State.LIVE);

		documentCache.init("documentCache" ,docInit ,docLimit);
		documentCache.setState(LRUCache.State.LIVE);
		
		facetCache.init("facetCache" ,facetDocInit ,facetDocLimit);
		facetCache.setState(LRUCache.State.LIVE);
		
		try {
			
			if(refreshReader != null) {
				this.rawReader = refreshReader;
				this.reader = this.rawReader;
				this.searcher = new IndexSearcher(reader);
				isSearcherCreate = true;
				//taxo ó��
				if(refreshTaxoReader != null && model.getFacetConfig() != null){
					this.taxoReader = refreshTaxoReader;
					this.fConfig = createFacetsConfig(model.getFacetsConfig());
					isTaxonomyReaderCreate = true;
				}
				
			} else {
				//searcher ����
				String indexPath = getQdbIndexPath(model.getQdbConfig(), indexDir, true);
				File f = new File(indexPath);
				String[] files = f.list();
				if(files.length == 0){
					//���丮 ���� ������ �� ������ �������ش�.
					try {
						createEmptyQdbIndex(indexPath, model.getQdbConfig());
					} catch (Exception e) {
						// TODO Auto-generated catch block
						LoggerEngine.error("Error on Create Empty Index. "+qdb, e);
					}
				}
				this.rawReader = openDirectoryReader(indexPath);
				//�ʿ����� ���� ��� Wrapping Directory�� ����� �� �ִ�. ����� �⺻ rawReader (DirectoryReader) ���
				this.reader = this.rawReader;
				this.searcher = new IndexSearcher(reader);
				isSearcherCreate = true;
				
				//taxonomy ����
				if(model.getFacetConfig() != null){
					String taxoPath = getQdbTaxonomyPath(model.getQdbConfig(), indexDir, true);
					f = new File(taxoPath);
					if(f.list().length == 0){
						//���丮 ���� ������ �� ������ �������ش�.
						try {
							createEmptyQdbTaxonomy(indexPath, model.getQdbConfig());
						} catch (Exception e) {
							// TODO Auto-generated catch block
							LoggerEngine.error("Error on Create Empty Taxonomy. "+qdb, e);
						}
					}
					this.taxoReader = openTaxonomyReader(taxoPath);
					this.fConfig = createFacetsConfig(model.getFacetsConfig());
					isTaxonomyReaderCreate = true;
				}
			}
			//Dynmaic Config Load �߰� by yonghw 20200212
			try{
				makeDynamicConfig();
//				this.dynamicFieldConfig.entrySet().forEach(k->System.out.println(k.getValue().getId() + ":" + k.getValue().getDataType()));
			} catch (Exception e) {
				new QException(QError.SEARCHER_CREATE_DYNAMIC_CONFIG, QError.SEARCHER_CREATE_DYNAMIC_CONFIG_MSG, e).logError();
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			new QException(QError.SEARCHER_CREATE_FAIL, QError.SEARCHER_CREATE_FAIL_MSG, e).logError();
		} 
		
		Facetconfig facetconfig = model.getFacetsConfig();
		if(facetconfig != null) {
			long ssdvCreateTime = System.currentTimeMillis();
			for(Facetconfig.Facet facet :  facetconfig.getFacet()) {
				//json�� ���� by yonghw 20200210
				//--����-- Json ���� �ʵ� ���ܽ�Ű��, �����ʵ带 Facet�� �߰��Ѵ� by yonghw 20200210
				Fieldconfig.Field jsonField = QDBConfigHandler.getInstance().getConfig(qdb).getFieldconfig(facet.getId());
				if(jsonField != null && 
						jsonField.getDataType().equals(QubeCore.DataType.JSON.name())) {
					//���� �߰��� �ʵ�鿡 Facet ��� �ʵ尡 ������ �߰��Ѵ�.
					dynamicFieldConfig.entrySet().stream()
					.filter(f->f.getValue().getId().startsWith(facet.getId()))
					.forEach(ff->makeSsdvStateCache(ff.getValue().getId()));
					//facet ���� �߰��ϱ�
					continue;
				}
				//--��--
				if(facet.getDim() == null && facet.getData() != null) {
					//2018-07-03 SortedSetDocValues Reader State �ʱ�ȭ �߰� by ktKim
					makeSsdvStateCache(facet.getId());
				}
			}
			LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher SSDVReaderState Create Complete(Time:" +(System.currentTimeMillis()-ssdvCreateTime)+"ms)");
		}
		
		//�̹��������� ���� ��� �̹��� �˻��� ���� �غ� ��.
		if(model.getImageConfig() != null && model.getImageConfig().isSetImages()){
			boolean useImgSearchCache = model.getImageConfig().isUseSearchCache();
			
			//���μ����� ��� cache�� ������ ������ �ʵ��� ����
			String serverName = ServerConfigHandler.getInstance().getServerModel().getServerConfig().getName();
			if(ServerType.I_MASTER.getValue().equalsIgnoreCase(serverName) || ServerType.I_SLAVE.getValue().equalsIgnoreCase(serverName)){
				useImgSearchCache = false;
			}
			
			this.useNewImgCache = useNewImgCache;
			this.comparator = new ImageSortComparator(Integer.valueOf(this.indexDir), qdb, useImgSearchCache, reader, useNewImgCache, model);
			
			if(useImgSearchCache){
				comparator.createFeatureCache();
			}
		}
		//�޸� ���� ���.
		LoggerEngine.info(String.format(this.qdb+"[%s] QubeSearcher Created, Mem[max: %sKB, total: %sKB, free: %sKB, used: %sKB]"
				,this.indexDir
				,Tool.fcomma(Runtime.getRuntime().maxMemory()/1024)
				,Tool.fcomma(Runtime.getRuntime().totalMemory()/1024)
				,Tool.fcomma(Runtime.getRuntime().freeMemory()/1024)
				,Tool.fcomma((Runtime.getRuntime().totalMemory()-Runtime.getRuntime().freeMemory())/1024)
		));
		
		//ExcutorService ����
		if(executor == null) {
			try {
				int threadCnt = QubeCore.getMultiThreadCnt(qdb,false);
				LoggerEngine.info(qdb+" QubeSearcher ExcutorService ����, Pool Size : " + threadCnt);
				executor = Executors.newFixedThreadPool(threadCnt);
			} catch (Exception e) {
				int defaultThreadCnt = 8;
				LoggerEngine.error("Executor ���� �� MultiThreadCnt �ε� ���з� �⺻��("+defaultThreadCnt+")���� pool�� �����մϴ�." , e);
				executor = Executors.newFixedThreadPool(defaultThreadCnt);
			} 
		}
		
//		LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher ���� ("+isSearcherCreate+")"
//				+", QueryResultCache("+qrLimit+")"+", DocumentCache("+docLimit+")"+" ������ �Ϸ�Ǿ����ϴ�.");
		LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher ���� ("+isSearcherCreate+"), TaxonomyReader("+isTaxonomyReaderCreate+")"
				+", QueryResultCache("+qrLimit+")"+", DocumentCache("+docLimit+")"+", FacetCache("+facetDocLimit+")"+" ������ �Ϸ�Ǿ����ϴ�.");
	}
	
	
	/**
	 * @author : yonghw
	 */
	private void makeSsdvStateCache(String facetId) {
		try {
			ssdvStateCache.put(facetId, 
					new QubeSortedSetDocValuesReaderState(reader, qdb, this.dynamicFieldConfig, QDBConst.FACET_FIELD_PREFIX+facetId));
			if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\t"+this.qdb+" > "+facetId+" : SSDV Load.");
		}catch(Exception e){
			//new QException(QError.SEARCHER_CREATE_FAIL_NOT_SSDV_EXIST, QError.SEARCHER_CREATE_FAIL_NOT_SSDV_EXIST_MSG, e).logError();
			LoggerEngine.infoToDebug("���ε� SSDV�� ���� �����ϴ�.", e);
		}
	}
	
	
	/**
	 * Reader���� Qdb.xml �� ���� �ʵ�鿡 ���� Config�� ������ش�.
	 * ����: 
	 * 1. �������Ͽ��� ��ü �ʵ��� ����
	 * 2. xml Config���� Json Type�� Map<String, Field> ����
	 * 3. ��ü �ʵ��Ͽ��� xml Config�� ������ �ʰ�, Json Type �ʵ������ �����ϴ� ���
	 *    Dynamic Config�� �߰��Ѵ�. (xml Config���� ������ �ʵ带 Object Copy ��, ID�� DataType�� �ٲ㾴��.)
	 * 
	 * @author : yonghw
	 * @throws Exception 
	 * @revisionHistory
	 * 2020. 2. 12. - 
	 */
	private void makeDynamicConfig() throws Exception {
		//1. ��ü leave �� Ȯ���ؼ� Map�� ��´�. Map<String, FieldInfo>
		//.����
		Map<String, FieldInfo> totalMap = new HashMap<>();
		for(LeafReaderContext c : this.reader.leaves()) {
			com.giosis.qube.core.index.LeafReader leafReader = c.reader();
			FieldInfos fieldInfos = leafReader.getFieldInfos();
			Iterator<FieldInfo> itr = fieldInfos.iterator();
			while(itr.hasNext()) {
				FieldInfo info = itr.next();
				totalMap.put(info.name, info);
			}
		}
		
		//2. ����� Json fieldConfig�� Ȯ��
		Map<String, Field> staticConfig = 
		QDBConfigHandler.getInstance().getConfig().get(qdb).getFieldconfig();
		
		//FieldType�� Json�� ����� �߸���.
		Map<String, Field> jsonFieldConfig = 
				staticConfig.entrySet().stream()
		.filter(f->f.getValue().getDataType().equals(QubeCore.DataType.JSON.name()))
		.collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		
		//totalMap�� Ű ���� ���� �ʵ��� ���
		Iterator<Entry<String, FieldInfo>> itr = totalMap.entrySet().iterator();
		
		//3. reader �ʵ� ��ȸ
		while(itr.hasNext()) {
			Entry<String, FieldInfo> entry = itr.next();
			//indexed fieldName
			String fieldName = entry.getKey();
			FieldInfo fieldInfo = entry.getValue();
			
			/*//�ʵ���� $�� �����ϴ°�� Facet
			if(fieldName.indexOf(QDBConst.FACET_FIELD_PREFIX) == 0) {
				//�� �� $ ����
				String facetName = fieldName.substring(1);
				//���� config�� ������, JsonConfig�� �ش�Ǵ��� Ȯ��
				if(staticConfig.get(facetName) == null) {
					Optional<Entry<String, Field>> optional =
							jsonFieldConfig.entrySet().stream()
							.filter(f-> facetName.indexOf(f.getKey()) == 0).findAny();
					if(optional.isPresent()) {
						Facet facet = new Facet();
						//����� facet id�� ����
						facet.setId(facetName);
						dynamicFacetConfig.put(facetName, facet);
					} else {
						//����ó��(?)
					}
				}
			}
			//xml Config�� ����, Json Type�� �̸����� �����ϴ� ���
			else*/ 
			if(staticConfig.get(fieldName) == null) {
				Optional<Entry<String, Field>> optional =
				jsonFieldConfig.entrySet().stream()
				//���ε� �ʵ尡 Json �ʵ������ �����ϴ� ��� ex) "JSON_ARRAY.T_PV".startsWith ("JSON_ARRAY")
				.filter(f-> fieldName.startsWith(f.getKey())).findAny();
				if(optional.isPresent()) {
					//���� �ʵ带 �����Ѱ� ���(Deep Copy)
					//option.get().getValue() -> jsonFieldConfig�� Field
					Field f = (Field) ObjectCopy.clone(optional.get().getValue());
					f.setId(fieldName);
					f.setDataType(findJsonType(fieldInfo).name());
					/*DataType dataType = findJsonType(fieldInfo);
					f.setDataType(dataType.name());
					// float �̳� date ���� analyzer�� white space�� ��� 
					if(dataType != DataType.VARCHAR) {
						f.setAnalyzer(QDBConst.AnalyzeType.WHITESPACE.name());
					} 
					*/
					this.dynamicFieldConfig.put(fieldName, f);
				} else {
					//����ó��(?)
				}
			}
		}
		
	}
	
	private DataType findJsonType(FieldInfo fieldInfo) {
		if(fieldInfo.getPointNumBytes() == Float.BYTES) {
			return DataType.FLOAT;
		}
		else if(fieldInfo.getPointNumBytes() == Long.BYTES) {
			return DataType.DATE;
		} 
		else if(fieldInfo.getPointNumBytes() == 0) {
			return DataType.VARCHAR;
		} else {
			throw new QException(QError.JSONCONFIG_VALIDATION_TYPE_ERROR, QError.JSONCONFIG_VALIDATION_TYPE_ERROR_MSG);
		}
	}
	
	public Map<String, Field> getDynamicFieldConfig() {
		return dynamicFieldConfig;
	}

	public final String getQdb(){
		return this.qdb;
	}
	
	/** Raw reader (no fieldcaches etc). Useful for operations like addIndexes */
	public final DirectoryReader getRawReader() {
		return rawReader;
	}
	
	public final DirectoryReader getIndexReader() {
		assert reader == searcher.getIndexReader();
		return reader;
	}
	
	public final IndexSearcher getIndexSearcher() {
		return searcher;
	}
	
	public final DirectoryTaxonomyReader getTaxonomyReader() {
		return taxoReader; 
	}
	
	public void setWarmupQueries(List<WarmUpQuery> warmupQueries){
		this.warmupQueries = warmupQueries;
	}
	
	public List<WarmUpQuery> getWarmupQueries(){
		return this.warmupQueries;
	}
	
	public synchronized void close(boolean useClearImgCache,
			boolean readerClose, boolean taxoReaderClose) throws QException {
		
		String indexDir = QDBConfigHandler.getInstance().getIndexDir(qdb);
		try {
			if(readerClose) {
				reader.close();
				if(reader != rawReader) 
					rawReader.close();
			}
			if(taxoReaderClose) {
				if(taxoReader != null) 
					taxoReader.close();
			}
			
			if(comparator != null){
				if(useClearImgCache) comparator.clearFeatureCache();
				comparator.close();
			}
			LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") close �Ϸ�");
		} catch (Exception e) {
			throw new QException(QError.SEARCHER_FAIL_READER_CLOSE, QError.SEARCHER_FAIL_READER_CLOSE_MSG, e);
		} finally { 
			//null ó���� ���� ���ܸ� �������� �ּ� ó�� by jilee 2015-05-26
//			searcher = null;
//			reader = null;
//			directory = null;
			
			//ĳ�� Clear�� ����ó�� �߰� by jilee 2015-06-17
			try{
				queryResultCache.clear();
				documentCache.clear();
				facetCache.clear();
				ssdvStateCache.clear();	//���� �߰� by ktKim 2018-07-03
				LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") ĳ�� Clear �Ϸ�");
			}catch(Exception e){
				throw new QException(QError.SEARCHER_FAIL_CLEAR_CACHE, QError.SEARCHER_FAIL_CLEAR_CACHE_MSG+" ( "+qdb+"["+indexDir+"] )", e);
			}
		}
		
		//Executor ���� 
		if(executor != null) {
			if(!executor.isShutdown()) executor.shutdown();
			while(!executor.isTerminated()){
				try {
					executor.awaitTermination(1L, TimeUnit.SECONDS);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					LoggerEngine.error("Executor Terminamtion ��� �� ����", e);
				}
			}
			executor = null;
			LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") ExecutorService ���� �Ϸ�");
		}
		
		LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") �� ���� ���� �Ǿ����ϴ� (TotalSearch : "+getTotalSearchCnt()+" / CurrentSearch : " + getCurrentSearchCnt() +")");
	}
	
	public void warmup() throws Exception {
		QDBModel model = QDBConfigHandler.getInstance().getConfig(qdb);
		//warmup ��� ������ �Ǿ����� �� ���� by jilee 2014-12-04
		if(model != null && model.getQdbConfig().isUseWarmup()) {
			int warmupCnt=0, fileWarmupCnt=0;
			//���Ե� ������ Warmup
			if(warmupQueries != null) {
				for(WarmUpQuery q : warmupQueries){
					try{
						//					search(SearchMode.LISTNSET, query, null, null, 0, 100, true, 0);
						search(q.getMode(), q.getQ(), null, q.getSort(), q.getStart(),
								q.getRows(), q.isNeedScore(), 0);
						warmupCnt++;
					} catch (Exception e) {
						new QException(QError.SEARCHER_WARM_UP_SEARCH_ERROR,qdb + " " + QError.SEARCHER_WARM_UP_SEARCH_ERROR_MSG + "\n" + q.toString(), e).logError();
					}

				}
			}
			
			//���Ͽ� ������ ������ Warmup
			List<WarmUpQuery> fileWarmupQueries = getWarmupListByFile();
			if(fileWarmupQueries != null) {
				for(WarmUpQuery q : fileWarmupQueries) {
					try {
		//				search(SearchMode.LISTNSET, query, null, null, 0, 100, true, 0);
						search(q.getMode(), q.getQ(), null, q.getSort(), q.getStart(),
								q.getRows(), q.isNeedScore(), 0);
						fileWarmupCnt++;
					} catch (Exception e) {
						new QException(QError.SEARCHER_WARM_UP_FILE_SEARCH_ERROR,qdb + " " + QError.SEARCHER_WARM_UP_FILE_SEARCH_ERROR_MSG + "\n" + q.toString(), e).logError();
					}
				}
			}
			LoggerEngine.info(qdb+"["+indexDir+"] QDB New Searcher�� �ʱ�ȭ(Warmup)�� �Ϸ�Ǿ����ϴ�."
				+" Cached Memory: "+warmupCnt+"/"+ (warmupQueries != null ? warmupQueries.size() : 0)
				+" Cached File: "+fileWarmupCnt+"/"+(fileWarmupQueries != null ?fileWarmupQueries.size() : 0)
			);
		}else 
			LoggerEngine.info(qdb + "["+indexDir+"] QDB New Searcher�� �ʱ�ȭ(Warmup)�� ���� ���� �ʽ��ϴ�.");
		
	}
	
	private synchronized void addWarmupQuery(WarmUpQuery query){
		if(warmupQueries == null) warmupQueries = new CopyOnWriteArrayList<WarmUpQuery>();
		if(!warmupQueries.contains(query)){
			if(warmupQueries.size() < this.warmupSize){
				warmupQueries.add(query);
			}else{
				Iterator<WarmUpQuery> iter = warmupQueries.iterator();
				if(iter.hasNext()){
					WarmUpQuery q= iter.next();
					warmupQueries.remove(q);
				}
			}
		} /*else {
			LoggerEngine.info("[AddWarmupQuery] �̹� �����ϴ� ���� �Դϴ�. size: " + warmupQueries.size()
			+ " Query:" + query.toString());
		}*/
	}
	
	private List<WarmUpQuery> getWarmupListByFile(){
		List<WarmUpQuery> warmupQueries = new ArrayList<>();
		QDBModel model = QDBConfigHandler.getInstance().getConfig(qdb);
		String warmUpFile = QubeCore.getBaseIndexPath(model.getQdbConfig())+File.separator+"config"+File.separator+WARMUP_FILENAME;
		BufferedReader br = null;
		String line = null;
		try{
			if(!Tool.isEmpty(warmUpFile)){
				//stream open
				br = new BufferedReader(new InputStreamReader(new FileInputStream(warmUpFile)));					
				//�� �پ� �о��
				String [] r;
				while((line = br.readLine()) != null){
					line = line.toUpperCase();
					r = line.split(QueryConst.QUBE_DEF_SPLITER);
					warmupQueries.add(
//					[0]query [1]searchMode [2]sort [3]start [4]rows [5]needScore
							new WarmUpQuery(
								Parser.parseQuery(r[0].trim(), qdb, new Synonym(true), true, QueryConst.SEARCH_PARSE) 
								,SearchMode.valueOf(r[1])
								,Parser.parseSort(r[2], qdb)
								,Integer.valueOf(r[3])
								,Integer.valueOf(r[4])
								,Boolean.valueOf(r[5]))
					);
				}
			}else{
				LoggerEngine.info(qdb + "["+indexDir+"] Warmup ���� ����(����) ���� ( ���: " + warmUpFile + " )" );
			}
		}catch(Exception e){
			new QException(QError.SEARCHER_WARM_UP_FILE_READ_ERROR,qdb + ", " 
							+ QError.SEARCHER_WARM_UP_FILE_READ_ERROR_MSG 
							+ "\nline: " + line, e).logError();
		}finally {
			try {
				//stream close
				if (br != null) br.close();
			} catch (IOException e) {
				LoggerEngine.info(qdb + "["+indexDir+"] Warmup ���� ���� close ���� ( ���: " + warmUpFile + " )" );
			}
		}
		return warmupQueries;
	}
	
	public int maxDoc() {
		return this.reader.maxDoc();
	}
	
	public int numDocs() {
		return this.reader.numDocs();
	}
	
	public int numDeletedDocs() {
		return this.reader.numDeletedDocs();
	}
	
	
	public Document doc(int i, boolean useCache) throws QException{
		Document d = null;
		try {
			if (useCache && documentCache != null){
				d = documentCache.get(i);
				if (d != null) return d;
			}
			
			d = searcher.doc(i);
		} catch (Exception e) {
			LoggerEngine.error("reader.document(i)=" + i + "\n" + e.getMessage(), e);
		}
		
		if(documentCache != null) {
			documentCache.put(i, d);
		}
		return d;
	}
	
	public CollectionStatistics collectionStatistics(String field) throws IOException{
		CollectionStatistics stat = this.searcher.collectionStatistics(field);
		return stat;
	}
	
	/**
	 * {@link IndexSearcher} Low Level Basic Search
	 */
	public final void search(Query query, Filter filter, Collector collector) throws IOException{
		//Filter ����.
		Query finalQuery = null;
		if(filter != null){
			BooleanQuery.Builder builder = new BooleanQuery.Builder() ;
			builder.add(query, Occur.MUST);
			builder.add(filter, Occur.FILTER);
			finalQuery = builder.build();
		}else{
			finalQuery = query;
		}
		
		if(finalQuery == null) finalQuery = new MatchNoDocsQuery("Unavaliable Query = "+finalQuery);
		searcher.search(finalQuery, collector);
	}
	
	/**
	 * �˻� ��� {@link DocListAndSet} ����
	 * @param query
	 * @param filter
	 * @param sort
	 * @param start
	 * @param rows
	 * @param needScores
	 * @param timeLimit - 0���ϴ� Timeout ó�� X 
	 * @return {@link DocListAndSet}
	 * @throws QException
	 *  @author jilee
	 * <br/>- WINDOW SIZE�� ����� ������ �ʰ� ���� start ���� rows ���� ��ŭ�� �����ϵ��� ���� 2017-06-14
	 */
	public final DocListAndSet search(SearchMode mode, Query query, Filter filter, Sort sort, int start, int rows, boolean needScores, long timeLimit) throws Exception{
		//�˻��� ����� rows ������ ��� 
		int maxDocRequested = start + rows;
		if(maxDocRequested > reader.maxDoc()) maxDocRequested = reader.maxDoc();
		//�ּҰ� 1�� �����ϵ��� �߰� by jilee 2017-06-26
		if(maxDocRequested <= 0) maxDocRequested = 1; 

		//int supersetMaxDoc= maxDocRequested;

		//WINDOW_SIZE ��� ���ϵ��� ���� by jilee 2017-06-14
		//QUERY_RESULT_WINDOW_SIZE ������ �˻���� ��� (����� ������ 61�� ��� 70�� ���)
//		if (maxDocRequested < QueryConst.QUERY_RESULT_WINDOW_SIZE) {
//			supersetMaxDoc = QueryConst.QUERY_RESULT_WINDOW_SIZE;
//		} else {
//			supersetMaxDoc = ((maxDocRequested - 1) / QueryConst.QUERY_RESULT_WINDOW_SIZE + 1) * QueryConst.QUERY_RESULT_WINDOW_SIZE;
//			if (supersetMaxDoc < 0) supersetMaxDoc = maxDocRequested;
//		}
		
		//Collector ����.
		Collector finalCollector = null;
		TopDocsCollector<?> topCollector = null;
		DocSetCollector setCollector = null;
		FacetsCollector facetCollector = null;
		if(mode == SearchMode.LISTNSET || mode == SearchMode.LISTONLY){
			//���� Row����� ������ Collector ����
			if(sort == null && !needScores){
				//�⺻ Score �������� ���� �˻� : ������ ���� Score ���⵵ ���� ���
				topCollector = TopScoreDocCollector.create(maxDocRequested);
			}else{
				if(sort == null) sort = Sort.RELEVANCE; //������ ���� ��� 
				boolean fillFields = true;
				topCollector = TopFieldCollector.create(sort, maxDocRequested, fillFields, needScores, needScores);
			}
			
			//��ü ��� DocIdSet ��û ���ο����� ����
			if(mode == SearchMode.LISTNSET){
				//�˻� ��� ��ü DocIdSet�� �����ϴ� Collector �߰��� ����
				/*setCollector = new DocSetCollector(maxDoc());
				finalCollector = MultiCollector.wrap(topCollector,setCollector);*/
				//docIdSet ��� ����� ���� Collection���� �ʵ��� �ּ�
				finalCollector = topCollector;
			}else{
				finalCollector = topCollector;
			}
		} 
		else if(mode == SearchMode.TOPDOCSONLY) {
			//��ü score�� ��� ����
//			topCollector = TopScoreDocCollector.create(reader.maxDoc());
			//DocIndexOrder�� ��ü ��� Collect
			topCollector = TopFieldCollector.create(new Sort(SortField.FIELD_DOC), maxDoc(), false, false, false);
			finalCollector = topCollector;
		}
		else if(mode == SearchMode.LEAFDOCS) {
			//���׸�Ʈ�� DocIdSet
			facetCollector = new FacetsCollector();
//			finalCollector = fc;
		} else {
			//�˻� ��� ��ü DocIdSet�� �����Ͽ� Collector ����
			setCollector = new DocSetCollector(maxDoc());
			finalCollector = setCollector;
		}
		
		//Timeout ������ ���� ��� Collector ����
		if(timeLimit > 0){
			finalCollector = new TimeLimitingCollector(finalCollector, TimeLimitingCollector.getGlobalCounter(), timeLimit);
		}
		//Collector ���� ��
		
		long stime = System.nanoTime();
		search(query, filter, finalCollector);
		
		addWarmupQuery(new WarmUpQuery(query, mode, sort, start, rows, needScores));
		long timeIndexSearch = (System.nanoTime()-stime);
		
		stime = System.nanoTime();
		//Collector�� ������ ����� DocListAndSet����
		DocListAndSet ret = new DocListAndSet();
		
		//LEAFDOCS �߰� by yonghw 20180814
		if(mode == SearchMode.LEAFDOCS) {
			ret.matchingDocsList = facetCollector.getMatchingDocs();
		}
		if(mode == SearchMode.TOPDOCSONLY) {
			ret.topDocs = topCollector.topDocs();
		}
		if(mode == SearchMode.LISTNSET || mode == SearchMode.SETONLY){
			ret.docSet = setCollector == null ? null : setCollector.getDocSet();
		}
		
		if(mode != SearchMode.SETONLY && mode != SearchMode.LEAFDOCS && mode != SearchMode.TOPDOCSONLY){
			//Top Result�� �䱸 �Ǵ� �˻� ��忡���� DocList�� �������ش�.
			
			//2018-07-12 ó������ �˻��� �ƴ϶� start ���� Topdoc���� �������� ���� by ktKim
			//TopDocs top = topCollector.topDocs(0, maxDocRequested);
			TopDocs top = topCollector.topDocs(start, maxDocRequested);
			int totalHits = topCollector.getTotalHits(); //�� �˻���� �Ǽ�
			float maxScore = totalHits > 0 ? top.getMaxScore() : 0.0f; //�ִ� ������.
			int nDocsReturned = top.scoreDocs.length; //��ȯ��� �Ǽ�

			int ids[] = new int[top.scoreDocs.length];
			float scores[] = needScores ? new float[nDocsReturned] : null;
			Object fieldValues[][] = (topCollector instanceof TopFieldCollector) ? new Object[nDocsReturned][] : null;
			for(int i=0; i<nDocsReturned; i++){
				ScoreDoc doc = top.scoreDocs[i];
				ids[i] = doc.doc;
				if(scores != null) scores[i] = doc.score;
				if(fieldValues != null){
					//���Ŀ��� ����� �ʵ� �� �� 
					FieldDoc fieldDoc = (FieldDoc)doc;
					if(fieldDoc.fields != null) fieldValues[i] = fieldDoc.fields;
				}
			}
			
			int sliceLen = Math.min(maxDocRequested, nDocsReturned);
			if (sliceLen < 0) sliceLen=0;
			if(fieldValues != null){
				ret.docList = new FieldDocSlice(0, sliceLen, ids, scores, totalHits, maxScore, fieldValues);
			}else{
				ret.docList = new DocSlice(0, sliceLen, ids, scores, totalHits, maxScore);
			}
		}
		
		return ret;
	}
	
	public QubeSearchContainer search(SearchMode mode, Query query, Filter filter, Sort sort, int start, int rows, boolean useCache, boolean needScores, boolean usePartialMatch, long timeLimit) throws QException{
		QubeSearchContainer ret = new QubeSearchContainer();
		QueryResultKey key = null;
		DocList superSet = null;
		DocList subSet = null;
		DocListAndSet docListAndSet = null;
		
		if (useCache && queryResultCache != null) {
			try {
				key = new QueryResultKey(query, sort, start, rows);
			} catch (Exception e) {
				throw new QException(QError.SEARCHER_CREATE_CACHE_KEY_ERROR, QError.SEARCHER_CREATE_CACHE_KEY_ERROR_MSG, e);
			}
			docListAndSet = queryResultCache.get(key);
			if(docListAndSet != null){
				if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] QueryResult Cache Load. key="+key);
				superSet = docListAndSet.docList;
				if(superSet != null){
					//�Ϲ� �˻��� superSet�� start, rows ����ŭ������� ĳ�� �ǹǷ� subset��� X
//					subSet = superSet.subset(start, rows);
//					if(subSet != null){
//						if(superSet instanceof DocSlice){
//							ret.setMatcheDocCnt(((DocSlice)superSet).matches);
//							ret.setReturnDocCnt(((DocSlice)superSet).len);
//						}
//						ret.setDocList(subSet);
//						ret.setDocSet(docListAndSet.docSet);
//						return ret;
//					}
					if(superSet instanceof DocSlice){
						ret.setMatcheDocCnt(((DocSlice)superSet).matches);
						ret.setReturnDocCnt(((DocSlice)superSet).len);
					}
					ret.setDocList(superSet);
					ret.setDocSet(docListAndSet.docSet);
					return ret;
				}
			}
		}
		
		try {
			
			docListAndSet = search(mode, query, filter, sort, start, rows, needScores, timeLimit);
			superSet = docListAndSet.docList;
			if (key != null && superSet.size() <= Integer.MAX_VALUE ) {
				queryResultCache.put(key, docListAndSet);
			}
			
			if(superSet instanceof DocSlice){
				ret.setMatcheDocCnt(((DocSlice)superSet).matches);
				ret.setReturnDocCnt(((DocSlice)superSet).len);
			}
			//2018-07-12 subset ������� �ʵ��� ���� by ktKim
			//ret.setDocList(superSet.subset(start, rows));
			ret.setDocList(superSet);
			ret.setDocSet(docListAndSet.docSet);
		} catch (Exception e) {
			// TODO Auto-generated catch block
			throw new QException(QError.SEARCHER_SEARCH_ERR, QError.SEARCHER_SEARCH_ERR_MSG, e);
		}
		
		return ret;
	}
	
	/**
	 * �̹��� �˻�
	 *  
	 * @param imgSrcName
	 * @param imgBinaryField
	 * @param query
	 * @param filter
	 * @param start
	 * @param rows
	 * @param timeLimit
	 * @return
	 * @throws QException
	 * @throws Exception
	 */
	public QubeSearchContainer search(String imgSrcName, String imgBinaryField, String algorithmId, Query query, Filter filter, int start, int rows, long timeLimit, 
			int multiCnt, boolean useSimilarityScore, float topRate, float msCutline, boolean isPrintDetail, boolean useCache) throws QException, Exception{
		
		//��� �ð� ����. ���絵 ����� �غ� �ð��� INFO�� ����ϵ��� �Ѵ�. 
		long stime = 0l, docsettime = 0l, loadtime = 0l;
		stime = System.nanoTime();
		
		QubeSearchContainer ret = new QubeSearchContainer();
		QueryResultKey key = null;
		DocList superSet = null;
		DocList subSet = null;
		DocListAndSet docListNSet = null;
		
		if (queryResultCache != null) {
			try {
				key = new QueryResultKey(query, imgBinaryField, algorithmId, imgSrcName);
			} catch (Exception e) {
				throw new QException(QError.SEARCHER_CREATE_CACHE_KEY_ERROR, QError.SEARCHER_CREATE_CACHE_KEY_ERROR_MSG, e);
			}
			docListNSet = queryResultCache.get(key);
			if(docListNSet != null && useCache){
				if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] DocListNSet From QueryResultCache. key="+key);
				superSet = docListNSet.docList;
				if(superSet != null){
					//�̹����˻��� �˻���� ��ü�� �����ϰ� �־� subset���� ĳ�ð���� ��
					subSet = superSet.subset(start, rows);
					if(subSet != null){
						if(superSet instanceof DocSlice){
							ret.setMatcheDocCnt(((DocSlice)superSet).matches);
							ret.setReturnDocCnt(((DocSlice)subSet).len);
						}
						ret.setDocList(subSet);
						//DocSet�� ������� �ʾ� �ּ�
//						ret.setDocSet(docListNSet.docSet);
						return ret;
					}
				}
			}
		}
		
		BufferedImage imgBuf = null;
		try {
			
			/**
			 * TopDocs�� �̹������絵 ����ϱ� ���� �˻�
			 */
//			docListNSet = search(SearchMode.TOPDOCSONLY, query, filter, null, start, rows, false, timeLimit);
//			int totalHits =  docListNSet.topDocs.totalHits;
			
			/**
			 * DocSet���� �̹������絵 ����ϱ� ���� �˻�
			 */
			docListNSet = search(SearchMode.SETONLY, query, filter, null, start, rows, false, timeLimit);
			int totalHits =  docListNSet.docSet.size();
			if (key != null && totalHits <= Integer.MAX_VALUE ) {
				queryResultCache.put(key, docListNSet);
			}
			
			docsettime = System.nanoTime() - stime;
			
			//�̹��� �ε�
			imgBuf = ImgUtil.getBufferedImage(imgSrcName);
			loadtime = System.nanoTime()-docsettime-stime;
			
			//�̹��� ������¡
			try {
				if (Math.max(imgBuf.getHeight(), imgBuf.getWidth()) > QubeImageBulider.MAX_IMAGE_DIMENSION) {
						imgBuf = ImageUtils.scaleImage(imgBuf, QubeImageBulider.MAX_IMAGE_DIMENSION);
	            }
			} catch(Exception e) {
				throw new QException(QError.PARSER_IMAGE_ERR, QError.PARSER_IMAGE_RESIZE_ERROR, 
							"Image = "+imgSrcName ,e);
			}
			
			LoggerEngine.infoToDebug("\t"+query+"\tDocSet "+Tool.fcomma(totalHits)+"�� ���絵 ���� �غ� �Ϸ�[ms] (DocSet,ImgLoad,ImgScale)\t"+Tool.nanoToMilli(docsettime)+"\t"+Tool.nanoToMilli(loadtime)+"\t"+Tool.nanoToMilli(System.nanoTime()-docsettime-loadtime-stime));
			
			//���絵 ��� �� ���� ��� ȹ�� ����
			DocListAndSet imgResult = comparator.search(imgBuf, imgBinaryField, algorithmId, docListNSet, multiCnt, useSimilarityScore, topRate, msCutline, isPrintDetail);
			
			//null ó�� �߰� topDocs ���x
			docListNSet.topDocs = null;
			
			superSet = imgResult.docList;
			subSet = superSet.subset(start, rows);
			if(superSet instanceof DocSlice){
				ret.setMatcheDocCnt(((DocSlice)superSet).matches);
				ret.setReturnDocCnt(((DocSlice)subSet).len);
			}
			//ret.setDocList(imgResult.docList);
			//ret.setDocList(superSet);
			ret.setDocList(subSet);
//			ret.setDocSet(docSet);
		} catch (QException e) {
			throw e;
		}
		catch (Exception e) {
			// TODO Auto-generated catch block
			throw new QException(QError.SEARCHER_IMGSEARCH_ERR, QError.SEARCHER_IMGSEARCH_ERR_MSG, e);
		}finally {
			if(imgBuf != null) {
				imgBuf.flush();
				imgBuf = null;
			}
		}
		
		return ret;
	}
	
	/**
	 * facet �˻�
	 * - facet �� ���� Ƚ�� = facet.query�� ���� * (facet.field�� ���� + facet.math�� ����) 
	 * @param ret
	 * @param queryContainer
	 * @param queries
	 * @param filter
	 * @param collates
	 * @param maths
	 * @param offset
	 * @param limit
	 * @param minCount
	 * @param useCache
	 * @throws Exception
	 */
	public void facetSearch(QubeQueryResult ret, QueryContainer queryContainer, Query[] queries, Filter filter, FacetCollate[] collates, FacetCollate[] maths, int offset, int limit, int minCount, boolean useCache) throws Exception{
		
		//Facet�� �������� �ʴ� QDB�� ��� Error Return
		if( QDBConfigHandler.getInstance().getConfig(qdb).getFacetsConfig() == null){
			throw new QException(QError.PARSER_FACET_ERR, QError.PARSER_QDB_NOT_EXISTS_FACET_MSG);
		}
		FacetsConfig facetsConfig = QubeCore.createFacetsConfig(QDBConfigHandler.getInstance().getConfig(qdb).getFacetsConfig());
		
		//Facet�۾��� ���� ��ɵ� �� ����� �����ϱ����� �ʱ⿡ ����
		List<NamedList<String>> facetGroupResults = new ArrayList<>();
		List<NamedList<String>> facetMathResults = new ArrayList<>();
		List<List<FacetNode>> facetTaxoResults = new ArrayList<>();
		
		/**
		 * 1. facet.field�� �з�
		 * - SortedSet, Taxonomy facet�������� �з�
		 * - math������ SortedSet Facet����� �߰��� ���� ���� �� (�� Taxo������ X)
		 */
		ArrayList<FacetCollate> groupList = new ArrayList<>();
		ArrayList<FacetCollate> taxoList = new ArrayList<>();
		FacetCollate[] groups = null;
		FacetCollate[] taxos = null;
		//taxo list�� ������ �߰��ϸ鼭 ��� X
		//boolean[] taxoFieldIndex = null;	//Result�� ������ �°� ������ �ֵ��� ���� �߰� by ktKim
		if(collates != null) {
			//taxoFieldIndex = new boolean[collates.length];
			for(int i=0;i < collates.length;i++){
				String field = collates[i].getField();
				//Parser���� Field��ȿ���� �̸� üũ�ϱ� ������ �ּ� by jilee 2019-06-17
//				if(qdbFacetConfig.get(field) == null){
//					//Error Msg �߰� ���� ����(Parser���� Check��)
//					throw new QException(QError.PARSER_NOT_SUPPORT_FIELD, QError.PARSER_NOT_SUPPORT_FIELD_MSG, field);
//				}
				if(facetsConfig.getDimConfig(field).hierarchical) {
					//taxoFieldIndex[i] = true;
					collates[i].setType(FacetCollate.FACET_TYPE_TAXONOMY);
					taxoList.add(collates[i]);
				}else {
					//taxoFieldIndex[i] = false;
					groupList.add(collates[i]);
				}
			}
		}
		
		if(groupList.size() > 0) groups = groupList.stream().toArray(FacetCollate[]::new);
		if(taxoList.size() > 0) taxos = taxoList.stream().toArray(FacetCollate[]::new);
		
		/**
		 * 2. ������ ��ŭ Facet���� ����
		 */
		for(Query query : queries) {
			//�˻� ��� Collector�� ����
			FacetsCollector fc = null;
			FacetResultPerType facetResultPerType = null;
			
			/**
			 * 3. SortedSetDocValues�� Facet �˻�
			 * - ������ �� �ʵ忡 ���� Group, Math ������ ����
			 * - 
			 */
			if(groups != null || maths != null) {
				/**
				 * 3.1 facet.field, facet.math cache ��� Ȯ��
				 */
				FacetResultCache cachedGroup = facetCache(query, filter != null ? filter : null, groups, offset, limit, minCount, useCache);
				if(cachedGroup != null) {
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] QubeFacetResult From GroupCache");
					//ret.setFacetList(fieldFacetResult.getSortedFacet());
					for(NamedList<String> facetResult : cachedGroup.getSortedFacet()) {
						facetGroupResults.add(facetResult);
					}
				}
				
				FacetResultCache cachedMath = facetCache(query, filter != null ? filter : null, maths, offset, limit, minCount, useCache);
				if(cachedMath != null) {
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] QubeFacetResult From MathCache");
					//ret.setFacetMathList(fieldFacetMathResult.getSortedFacet());
					for(NamedList<String> facetResult : cachedMath.getSortedFacet()) {
						facetMathResults.add(facetResult);
					}
				}
				
				/**
				 * 3.2 cache�� ���� ��� �˻� ���� 
				 * Cache ȣ�� ���ο� ���� Facet ������ �� Field�� Parameter �����ϴ� ����� �޶����� ������ �����Ͽ� ȣ��
				 * (Facet ���� �� ��� �ʵ带 �־� �ѹ��� ���ϱ� ���Ͽ� ���)
				 */
				if( (groups != null && cachedGroup == null) 
				|| (maths != null && cachedMath == null) ) {	//Group �Ǵ� Math�� �ϳ��� Ÿ�� ���� ���
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] Start create facet by ssdv ...");
					//�˻� ��� Collector�� ����
					if(fc == null) {
						long fcTime = 0l;
						fc = new FacetsCollector();
						if(LoggerEngine.isDebugEnabled()) fcTime = System.currentTimeMillis();
						search(query, filter != null ? filter : null, fc);
						if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\tFacetCollector create time : " + (System.currentTimeMillis() - fcTime) + "ms");
					}
					
					/**
					 * group�̳� math cache���� ������ ����� collate�� null�� �Է½��� Facet������ ���� �ʵ��� �Ѵ�
					 */
					facetResultPerType = sortedSetFacetSearch(queryContainer, fc, cachedGroup != null ? null : groups, cachedMath != null ? null : maths, offset, limit, minCount);
					
					//group ��� ���
					if(cachedGroup == null) {
						if(facetResultPerType.getGroupFacet().size() > 0) putFacetCache(query, filter != null ? filter : null, groups, offset, limit, minCount, new FacetResultCache(facetResultPerType.getGroupFacet()));
						//ret.setFacetList(facetResultPerType.getGroupFacet());
						for(NamedList<String> facetResult : facetResultPerType.getGroupFacet()) {
							facetGroupResults.add(facetResult);
						}
					}
					
					//math ��� ���
					if(cachedMath == null) {
						if(facetResultPerType.getMathFacet().size() > 0) putFacetCache(query, filter != null ? filter : null, maths, offset, limit, minCount, new FacetResultCache(facetResultPerType.getMathFacet()));
						//ret.setFacetMathList(facetResultPerType.getMathFacet());
						for(NamedList<String> facetResult : facetResultPerType.getMathFacet()) {
							facetMathResults.add(facetResult);
						}
					}
				}
			}
			
			/**
			 * 2. TaxonomyIndex�� ����� Facet �˻�
			 * - ���� �ʵ带 Ʈ�����·� �з��� ���ο��� Facet �˻�
			 */
			if(taxos != null) {
				long taxoFacetTime = 0l;
				if(LoggerEngine.isDebugEnabled()) {
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] Start create facet by taxonomy ...");
					taxoFacetTime = System.currentTimeMillis();
				}
				
				FacetResultCache cachedTaxo = facetCache(query, filter != null ? filter : null, taxos, offset, limit, minCount, useCache);
				if(cachedTaxo != null) {
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] QubeFacetResult Taxo Cache Load.");
					//ret.setFacetList(fieldFacetResult);
					//ret.setFacetTaxoList(taxoFacetCache.getTaxoFacet());
					facetTaxoResults = cachedTaxo.getTaxoFacet();
				}else {
					//�˻� ��� Collector�� ����
					if(fc == null) {
						fc = new FacetsCollector();
						long fcTime = 0l;
						if(LoggerEngine.isDebugEnabled()) fcTime = System.currentTimeMillis();
						search(query, filter != null ? filter : null, fc);
						if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\tFacet Collect Time : " + (System.currentTimeMillis() - fcTime) + "ms");
					}
					
					for(FacetCollate collate : taxos) {
						List<FacetNode> taxoFieldFacetResult  = taxonomyFacetSearch(fc, collate, offset, limit, minCount);
						facetTaxoResults.add(taxoFieldFacetResult);
					}
					
					putFacetCache(query, filter != null ? filter : null, collates, offset, limit, minCount, new FacetResultCache(facetTaxoResults, FacetCollate.FACET_TYPE_TAXONOMY));
				}
				
				if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\tTaxo Facet Time : " + (System.currentTimeMillis() - taxoFacetTime) + "ms");
			}
			
			/**
			 * ���� Facet ��� ����(Cache�� ����� ��쿡�� ������ Ÿ�� ����)
			 * TaxonomyField�� �Ȱ��� Facet.Field�� ������ ������ �����ϱ� ���Ͽ� ���
			 * [group taxo group(multivalue 4) group]�� ���
			 * 2��° TaxoField�� ���� �ϰ� ���������� ������ ���� GroupFacetField ����
			 */
			/*if(facetResult != null) {
				ArrayList<NamedList<String>> finalResult = new ArrayList<>();
				int ssdvCnt = facetResult != null ? facetResult.getGroupFacet().size() : 0;
				int taxoCnt = fieldFacetResult != null ? fieldFacetResult.size() : 0;
				int ssdvCnt = 0;	//FacetGroup Count 
				int taxoCnt = 0;	//TaxonomyFacet Count
				if(facetResult != null) {
					int[] multiValueCount = facetResult.getMultiValueCnt();
					for(int i=0;i < taxoFieldIndex.length;i++) {
						if(taxoFieldIndex[i]) {
							taxoCnt++;
						}else {
							for(int j=0;j<multiValueCount[i-taxoCnt];j++) {
								if(ssdvCnt < facetResult.getGroupFacet().size()) {
									finalResult.add(facetResult.getGroupFacet().get(ssdvCnt));
									ssdvCnt++;
								}
							}
						}
					}
					
				}
				ret.setFacetList(finalResult);
			}*/
		}
		
		ret.setFacetList(facetGroupResults.size() > 0 ? facetGroupResults : null);
		ret.setFacetMathList(facetMathResults.size() > 0 ? facetMathResults : null);
		ret.setFacetTaxoList(facetTaxoResults.size() > 0 ? facetTaxoResults : null);
	}
	
	private FacetNode calcFacetTree(FacetNode taxoResult, Facets facet, com.giosis.qube.core.facet.FacetResult result, String label) throws Exception{
		
		String[] facetPath = Arrays.copyOf(result.path, result.path.length+1);
		facetPath[result.path.length] = label;
		
		com.giosis.qube.core.facet.FacetResult pathFacet = facet.getTopChildren(1, result.dim, facetPath);
		if(pathFacet != null && pathFacet.childCount > 0) {
			pathFacet = facet.getTopChildren(pathFacet.childCount, result.dim, facetPath);
			for(int i=0;i<pathFacet.labelValues.length;i++){
				
				FacetNode voList = new FacetNode();
				voList.setLabel(pathFacet.labelValues[i].label);
				voList.setValue(String.valueOf(pathFacet.labelValues[i].value.intValue()));
				
				try {
					voList = calcFacetTree(voList, facet, pathFacet, pathFacet.labelValues[i].label);
				} catch (Exception e) {
					LoggerEngine.error("Taxonomy Facet Tree Calc Error.");
				}
				
				taxoResult.addList(voList);
			}
		}
		
		return taxoResult;
	}
	
	private List<FacetNode> taxonomyFacetSearch(FacetsCollector fc, FacetCollate collate, int offset, int limit, int minCount) throws Exception{
		ArrayList<FacetNode> facetTree = new ArrayList<>();
		
		Facets facets = new QubeTaxonomyFacet(collate, taxoReader, fConfig, fc, QubeCore.getMultiThreadCnt(qdb,false), executor);
		
		/**
		 * 1. �ֻ��� children ������� ����
		 */
		List<com.giosis.qube.core.facet.FacetResult> topChildren = facets.getAllDims(1);
		
		/**
		 * 2. �� children ����� ���� children ��� ����
		 */
		for(com.giosis.qube.core.facet.FacetResult topChild : topChildren){
			int facetLimit = topChild.childCount;
			if(limit <= 0) facetLimit = topChild.childCount;
			
			//���� �ð� ��� �߰� by jilee 2019-10-15
			
			//topChild�� ���� children ����
			//result = facet.getTopChildren(result.childCount, result.dim, result.path);
			topChild = facets.getTopChildren(facetLimit, topChild.dim, topChild.path);
			
			Instant s = Instant.MIN;
			Duration elapsed = Duration.ZERO;
			Duration total = Duration.ZERO;
			for(int i=0;i<topChild.labelValues.length;i++){
				
				FacetNode node = new FacetNode();
				node.setLabel(topChild.labelValues[i].label);
				node.setValue(String.valueOf(topChild.labelValues[i].value.intValue()));
				
				try {
					if(LoggerEngine.isDebugEnabled()) s = Instant.now();
					node = calcFacetTree(node, facets, topChild, topChild.labelValues[i].label);
					if(LoggerEngine.isDebugEnabled()) elapsed = Duration.between(s, Instant.now());
					if(LoggerEngine.isDebugEnabled()) {
						total = total.plus(elapsed);
						LoggerEngine.debug(node.getLabel()+" "+node.getList().size()+" : "+elapsed.toString());
					}
				} catch (Exception e) {
					LoggerEngine.error("Taxonomy Facet Tree Calc Error.");
				}
				
				facetTree.add(node);
				
			}
			if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("Total : "+total.toString());
		}
		
		return facetTree;
	}
	
	private FacetResultPerType sortedSetFacetSearch(QueryContainer queryContainer, FacetsCollector fc, FacetCollate[] groups, FacetCollate[] maths, int offset, int limit, int minCount) throws Exception{
		
//		long currentTime = System.currentTimeMillis();
		FacetResultPerType facetResult = new FacetResultPerType();
		
		//Facet ���� field, math�� ������ �ʵ���� ���� ���  
		if(groups == null && maths == null) return facetResult;
		
		int groupSize = groups != null ? groups.length : 0;
		int mathSize = maths != null ? maths.length : 0;
		int totalCollateSize = groupSize + mathSize;
		
		//1. Facet.math field ����
		//ExpandVarchar�̰�, mathField[i]�� JsonBinaryField�̸� ssdv�� ������� �����Ƿ� state�ε�� �����Ҽ� �ֵ��� 
		//JsonBinaryField ���θ� �迭�� ���� by yonghw 20180621
		for(int i=0;i<mathSize;i++) {
			if(queryContainer.isExpandVarchar() && queryContainer.getExpandVarchar().isJsonField(maths[i].getField())) {
				maths[i].setExpvarchar(true);
			}else {
				maths[i].setExpvarchar(false);
			}
		}
		
		//2. Facet.field�� Facet.math�� ����� FacetField�� ���� �̸� ������� SortedSetDocValueReaderState �� ����
		//DefaultSortedSetDocValuesReaderState [] states = new DefaultSortedSetDocValuesReaderState[facetFields.length];
		QubeSortedSetDocValuesReaderState [] states = new QubeSortedSetDocValuesReaderState[totalCollateSize];
		for(int i=0;i<totalCollateSize;i++) {
			FacetCollate collate;
			if(i>=groupSize) collate = maths[i-groupSize];
			else collate = groups[i];
			if(!collate.isExpvarchar()) states[i] = ssdvStateCache.get(collate.getField());
		}
		
//		long spanInit = System.currentTimeMillis() - (currentTime);
//		if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\t\tMethod Init Time : " + spanInit + "ms");
		
		//3. SortedSetField Facet ����(������ ���ÿ� Count ���� ����)
		QubeSortedSetFacet facet = new QubeSortedSetFacet(getQdb(), queryContainer, groups, maths, states, fc, totalCollateSize, executor);
		
		//IndexFieldName�� ���ε� ��� Facet ���� Get
		//4. ���� Facet ����� ���� �� Dimension(Facet Label) ���� ����
		List<QubeFacetResult> results = facet.getAllDims(offset, limit, minCount);
		facetResult.setMultiValueCnt(facet.getMultiValueCounts());
		
//		long spanFacetCalc = System.currentTimeMillis() - (currentTime + spanInit);
//		if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\t\tMethod facetCalc Time : " + spanFacetCalc + "ms");
		
		//Group ���
		for(int i = 0; i < groupSize ; i++){
			QubeFacetResult result = results.get(i);
			NamedList<String> list = new NamedList<>();
			if(result != null) {
				for(int j = 0; j < result.labelValues.length; j ++) {
					Number[] values = result.labelValues[j].values;
					String vals = String.valueOf(values[0].intValue());
					if(values.length > 1) {
						for(int k=1; k<values.length; k++) {
							vals = vals+String.format(",%.2f",values[k].doubleValue());
						}
					}
					list.add(result.labelValues[j].label, vals);
				}
			}
			facetResult.addGroupFacet(list);
		}
		
		//FacetCollate�� groupNo�� key �� ������ map
//		Map<Integer, NamedList<String>> mathGroupMap = new LinkedHashMap<>(); 
		Map<Integer, List<FacetMath>> mathGroupMap = new LinkedHashMap<>();
		
		
		//���� ���� ������ ��������, �� ����
		//Math ���, i �� groupSize���� ����
		for(int i = groupSize; i < results.size(); i ++) {
			QubeFacetResult result = results.get(i);
			int mathIndex = i - groupSize;
			
			int nowMathGroupN = maths[mathIndex].getFacetMathGroupNo();
			//map���κ��� math groupNo�� �ش��ϴ� namedList�� ���´�. 
			if(mathGroupMap.get(nowMathGroupN) == null)
				mathGroupMap.put(nowMathGroupN, new ArrayList<FacetMath>());
//			NamedList<String> nowNamedList = mathGroupMap.get(nowMathGroupN);
			List<FacetMath> nowNamedList = mathGroupMap.get(nowMathGroupN);
			
			if(result != null) {
				switch(maths[mathIndex].getMathType()) {
					case JSON_VARCHAR:
						for(QubeLabelAndValue lv : result.labelValues){
							FacetMath m = new FacetMath(FacetMathType.JSON_VARCHAR);
							m.setLabel(lv.label);
							m.setCnt(lv.values[FacetMath.JsonMathLabel.CNT.getNumber()].intValue());
							m.setSum(lv.values[FacetMath.JsonMathLabel.SUM.getNumber()].doubleValue());
							m.setMin(lv.values[FacetMath.JsonMathLabel.MIN.getNumber()].doubleValue());
							m.setMax(lv.values[FacetMath.JsonMathLabel.MAX.getNumber()].doubleValue());
							m.setAvg(lv.values[FacetMath.JsonMathLabel.AVG.getNumber()].doubleValue());
							m.setFacetCnt(lv.values[FacetMath.JsonMathLabel.FACETCNT.getNumber()].intValue());
							nowNamedList.add(m);
						}
						break;
					case ASTRISK: {
						FacetMath m = new FacetMath(FacetMathType.ASTRISK);
						m.setLabel(maths[mathIndex].getFacetMathLabel());
						m.setCnt(result.labelValues[FacetMath.FacetMathLabel.count.getNumber()].values[0].intValue());
						m.setSum(result.labelValues[FacetMath.FacetMathLabel.sum.getNumber()].values[0].doubleValue());
						m.setMin(result.labelValues[FacetMath.FacetMathLabel.min.getNumber()].values[0].doubleValue());
						m.setMax(result.labelValues[FacetMath.FacetMathLabel.max.getNumber()].values[0].doubleValue());
						m.setAvg(result.labelValues[FacetMath.FacetMathLabel.average.getNumber()].values[0].doubleValue());
						m.setFacetCnt(result.labelValues[FacetMath.FacetMathLabel.facet_count.getNumber()].values[0].intValue());
						nowNamedList.add(m);
						break;
					}
					default:
						FacetMath m = new FacetMath(FacetMathType.DEFAULT);
						//���� label ���� �ʿ�x, ��� �����Ҷ� label ���� ����
						m.setCnt(result.labelValues[FacetMath.FacetMathLabel.count.getNumber()].values[0].intValue());
						m.setSum(result.labelValues[FacetMath.FacetMathLabel.sum.getNumber()].values[0].doubleValue());
						m.setMin(result.labelValues[FacetMath.FacetMathLabel.min.getNumber()].values[0].doubleValue());
						m.setMax(result.labelValues[FacetMath.FacetMathLabel.max.getNumber()].values[0].doubleValue());
						m.setAvg(result.labelValues[FacetMath.FacetMathLabel.average.getNumber()].values[0].doubleValue());
						m.setFacetCnt(result.labelValues[FacetMath.FacetMathLabel.facet_count.getNumber()].values[0].intValue());
						
						m.setCountTotal(result.labelValues[FacetMath.FacetMathLabel.count_total.getNumber()].values[0].intValue());
						m.setSumTotal(result.labelValues[FacetMath.FacetMathLabel.sum_total.getNumber()].values[0].doubleValue());
						m.setMinTotal(result.labelValues[FacetMath.FacetMathLabel.min_total.getNumber()].values[0].doubleValue());
						m.setMaxTotal(result.labelValues[FacetMath.FacetMathLabel.max_total.getNumber()].values[0].doubleValue());
						m.setAvgTotal(result.labelValues[FacetMath.FacetMathLabel.average_total.getNumber()].values[0].doubleValue());
						m.setFacetCntTotal(result.labelValues[FacetMath.FacetMathLabel.facet_count_total.getNumber()].values[0].intValue());
						nowNamedList.add(m);
				}
			}
		}
		
		//��� �߰�, ���� �׷��ε� ����� �׷쳻 �����Ͽ�, namedList�� �����Ѵ�.
		ArrayList<NamedList<String>> mathFacet = new ArrayList<>();
		Iterator<Entry<Integer, List<FacetMath>>> itr = mathGroupMap.entrySet().iterator();
		FacetMathSort facetMathSort = queryContainer.getFacet().getFacetMathSort();
		while(itr.hasNext()) {
			Entry<Integer, List<FacetMath>> entry = itr.next();
			List<FacetMath> li = entry.getValue();
			
			FacetMath facetMath = null;
			if(li.size() > 0)
				//�����ִ� ���� Type�� �����Ƿ�, ù��° �󺧿��� Datatype�� ������
				facetMath = li.get(0);
			
			//����
			if(facetMathSort != null && li.size() > 0) {
				Collections.sort(li, facetMathSort.getComparator());
			}
			
			NamedList<String> nowNamedList = new NamedList<>();
			if(facetMath != null) {
				switch(facetMath.getMathType()) {
					case JSON_VARCHAR: case ASTRISK:
						for(FacetMath f : li){
							String t = "";
							t += f.getCnt() + ",";
							t += String.format("%.2f", f.getSum()) + ",";
							t += String.format("%.2f", f.getMin()) + ",";
							t += String.format("%.2f", f.getMax()) + ",";
							t += String.format("%.2f", f.getAvg()) + ",";
							t += f.getFacetCnt();
							nowNamedList.add(f.getLabel(), t);
						}
						break;
					default:
						nowNamedList.add(FacetMath.FacetMathLabel.count.name(), String.valueOf(facetMath.getCnt()));
						nowNamedList.add(FacetMath.FacetMathLabel.sum.name(), String.format("%.2f", facetMath.getSum()));
						nowNamedList.add(FacetMath.FacetMathLabel.min.name(), String.format("%.2f", facetMath.getMin()));
						nowNamedList.add(FacetMath.FacetMathLabel.max.name(), String.format("%.2f", facetMath.getMax()));
						nowNamedList.add(FacetMath.FacetMathLabel.average.name(), String.format("%.2f", facetMath.getAvg()));
						nowNamedList.add(FacetMath.FacetMathLabel.facet_count.name(), String.valueOf(facetMath.getFacetCnt()));
						nowNamedList.add(FacetMath.FacetMathLabel.count_total.name(), String.valueOf(facetMath.getCountTotal()));
						nowNamedList.add(FacetMath.FacetMathLabel.sum_total.name(), String.format("%.2f", facetMath.getSumTotal()));
						nowNamedList.add(FacetMath.FacetMathLabel.min_total.name(), String.format("%.2f", facetMath.getMinTotal()));
						nowNamedList.add(FacetMath.FacetMathLabel.max_total.name(), String.format("%.2f", facetMath.getMaxTotal()));
						nowNamedList.add(FacetMath.FacetMathLabel.average_total.name(), String.format("%.2f", facetMath.getAvgTotal()));
						nowNamedList.add(FacetMath.FacetMathLabel.facet_count_total.name(), String.valueOf(facetMath.getFacetCntTotal()));
				}
			}
			
			mathFacet.add(nowNamedList);
		}
		
		facetResult.setMathFacet(mathFacet);
//		long spanObject = System.currentTimeMillis() - (currentTime + spanInit + spanFacetCalc);
//		if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\t\tMethod facetObjejct Create Time : " + spanObject + "ms");
//		if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\tMethod SortedSetFacetSearch Time : " + (spanObject+spanInit + spanFacetCalc) + "ms");
		
		return facetResult;
	}
	
	public boolean isUseNewImgCache() {
		// TODO Auto-generated method stub
		return useNewImgCache;
	}
	
	@Override
	public String toString() {
		// TODO Auto-generated method stub
		StringBuilder builder = new StringBuilder();
		builder.append("QubeSearcher : ").append(qdb).append("["+indexDir+"]")
		.append("\t( Reader : Segments=").append(reader.getContext().isTopLevel ? reader.leaves().size() : 1)
		.append(" MaxDocs=").append(reader.maxDoc())
		.append(" NumDocs=").append(reader.numDocs())
		.append(" DeletedDocs=").append(reader.numDeletedDocs())
		.append(" )\n");
		return builder.toString();
	}
	
	/**
	 * Facet Cache���� Facet Search
	 * @param query
	 * @param filter
	 * @param field
	 * @param type
	 * @param offset
	 * @param limit
	 * @param minCount
	 * @param sort
	 * @param useCache
	 * @return
	 * @throws QException
	 */
	public FacetResultCache facetCache(Query query, Filter filter, FacetCollate[] collates, int offset, int limit, int minCount, boolean useCache) throws QException{
		if(facetCache != null && useCache){
			FacetResultKey key = null;
			try {
				key = new FacetResultKey(query, filter, collates, offset, limit, minCount);
			} catch (Exception e) {
				throw new QException(QError.SEARCHER_CREATE_FACET_CACHE_KEY_ERROR, QError.SEARCHER_CREATE_FACET_CACHE_KEY_ERROR_MSG, e);
			}
			return facetCache.get(key);
		}
		return null;
	}
	
	public void putFacetCache(Query query, Filter filter, FacetCollate[] collates, int offset, int limit, int minCount, FacetResultCache facetResult) throws QException{
		if(facetCache != null){
			FacetResultKey key = null;
			try {
				key = new FacetResultKey(query, filter, collates, offset, limit, minCount);
				facetCache.put(key, facetResult);
			} catch (Exception e) {
				throw new QException(QError.SEARCHER_CREATE_FACET_CACHE_KEY_ERROR, QError.SEARCHER_CREATE_FACET_CACHE_KEY_ERROR_MSG, e);
			}
		}
	}

	public int getCurrentSearchCnt() {
		return currentSearchCnt.get();
	}

	public void startCurrentSearchCnt() {
		currentSearchCnt.incrementAndGet();
	}
	
	public void endCurrentSearchCnt() {
		currentSearchCnt.decrementAndGet();
	}
	
	public boolean isClosePossible() {
		return currentSearchCnt.get() == 0;
	}

	public long getTotalSearchCnt() {
		return totalSearchCnt.get();
	}
	
	public void addTotalSearchCnt() {
		this.totalSearchCnt.incrementAndGet();
	}
	
	
	
	/*public void test() throws Exception{
		Terms terms = searcher.getIndexReader().getContext().leaves().get(0).reader().terms("U_SRCH_FIELD");
		TermsEnum tenum = terms.iterator();
		BytesRef term = null;
		while((term=tenum.next()) != null) {
			System.out.println(term.utf8ToString());
		}
	}*/
	
}
