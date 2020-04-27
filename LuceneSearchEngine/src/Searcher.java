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
 * Qube 검색기 - 텍스트, 바이너리, 이미지, Facet, Join 
 * @since Qube2.0
 * @author jilee - Lucene6.3.0기반으로 구현 2016-12-26
 *
 */
public class QubeSearcher extends QubeCore{
	private final String qdb;
	private final String indexDir;
	/**
	 * 다양한 기능을 위해 wrapping 된 reader 
	 */
	private DirectoryReader reader;
	/**
	 * reader를 이용한 작업시 reader wrapping으로 인한 Overhead 방지를 위해 이 Reader를 받아서 사용한다.
	 */
	private DirectoryReader rawReader; 
	/**
	 * Core Searcher
	 */
	private IndexSearcher searcher;
	/**
	 * Facet Search를 위한 TaxonomyReader
	 */
	private DirectoryTaxonomyReader taxoReader;
	private FacetsConfig fConfig;
	
	protected final LRUCache<QueryResultKey,DocListAndSet> queryResultCache = new LRUCache<QueryResultKey, DocListAndSet>();
	protected final LRUCache<Integer,Document> documentCache = new LRUCache<Integer, Document>();
	/**
	 * Facet결과 캐시 추가 by jilee 2017-09-04
	 * QueryResultCache설정과 동일하게 설정한다.
	 */
	//protected final LRUCache<FacetResultKey, List<List<QubeFacetResult>>> facetCache = new LRUCache<FacetResultKey, List<List<QubeFacetResult>>>();
	protected final LRUCache<FacetResultKey, FacetResultCache> facetCache = new LRUCache<FacetResultKey, FacetResultCache>();
	/**
	 * 2018-07-03 SSDV Cach 추가 2018-07-03 by ktKim
	 * * 참고 : 모든 FacetConfig에 지정된 필드의 QubeSortedSetDocValuesReaderState의 로드 시간이 다소 소요 되므로 Searcher 생성시 미리 캐시한다.
	 */
	protected final ConcurrentHashMap<String, QubeSortedSetDocValuesReaderState> ssdvStateCache = new ConcurrentHashMap<String, QubeSortedSetDocValuesReaderState>();
	
	private List<WarmUpQuery> warmupQueries=null;
	
	/**
	 * 이미지 검색
	 */
	private ImageSortComparator comparator = null;
	/**
	 * QubeSearch 생성시 새 이미지 캐시를 생성할지 여부
	 */
	private boolean useNewImgCache = true;
	private int warmupSize;
	
	/**
	 * 2018-08-30 Searcher Close를 위한 변수 추가 by ktKim
	 * currentSearchCnt = 현재 Searcher에서 검색하고 있는 Count
	 * totalSearchCnt = Searcher가 열리고 SearchUnit을 통해 총 검색요청을 한 Count
	 */
//	private volatile int currentSearchCnt;
	private AtomicLong totalSearchCnt = new AtomicLong(0);
	private AtomicInteger currentSearchCnt = new AtomicInteger(0);
	
	public static final String WARMUP_FILENAME="warm-up-query.txt";
	
	//Executor 
	private ExecutorService executor = null;
	
	/**
	 * QDB.xml 이 아닌 reader를 통해 추가된 필드정보
	 * 현재는 Json에서 사용 by yonghw 20200212 
	 */
	//Json 원문의 키로 시작하는, 모든 Json 필드들을 페싯으로 올려주면
	private Map<String, Fieldconfig.Field> dynamicFieldConfig = new HashMap<>();
	
	public QubeSearcher(String qdb, boolean useNewImgCache, DirectoryReader refreshReader, DirectoryTaxonomyReader refreshTaxoReader) {
		// TODO Auto-generated constructor stub
		boolean isSearcherCreate = false;
		//2017-11-16 facetReaderCreate by ktKim
		boolean isTaxonomyReaderCreate = false;
		this.qdb = qdb;
		this.indexDir = QDBConfigHandler.getInstance().getIndexDir(qdb);
		QDBModel model = QDBConfigHandler.getInstance().getConfig(qdb);
		
		//warmup size 설정
		this.warmupSize = model.getQdbConfig().getWarmupSize();
		
		int qrInit=0, qrLimit=0;
		int docInit=0, docLimit=0;
		int facetDocInit=0, facetDocLimit=0;
		
		//Cacheconfig qdbCacheConfig = model.getCacheConfig();
		//QDB Config에 값이 존재하지 않을 시 ServerCnfig의 Cache를 사용하도록 변경
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
				//taxo 처리
				if(refreshTaxoReader != null && model.getFacetConfig() != null){
					this.taxoReader = refreshTaxoReader;
					this.fConfig = createFacetsConfig(model.getFacetsConfig());
					isTaxonomyReaderCreate = true;
				}
				
			} else {
				//searcher 생성
				String indexPath = getQdbIndexPath(model.getQdbConfig(), indexDir, true);
				File f = new File(indexPath);
				String[] files = f.list();
				if(files.length == 0){
					//디렉토리 새로 생성시 빈 색인을 생성해준다.
					try {
						createEmptyQdbIndex(indexPath, model.getQdbConfig());
					} catch (Exception e) {
						// TODO Auto-generated catch block
						LoggerEngine.error("Error on Create Empty Index. "+qdb, e);
					}
				}
				this.rawReader = openDirectoryReader(indexPath);
				//필요기능이 있을 경우 Wrapping Directory를 사용할 수 있다. 현재는 기본 rawReader (DirectoryReader) 사용
				this.reader = this.rawReader;
				this.searcher = new IndexSearcher(reader);
				isSearcherCreate = true;
				
				//taxonomy 생성
				if(model.getFacetConfig() != null){
					String taxoPath = getQdbTaxonomyPath(model.getQdbConfig(), indexDir, true);
					f = new File(taxoPath);
					if(f.list().length == 0){
						//디렉토리 새로 생성시 빈 색인을 생성해준다.
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
			//Dynmaic Config Load 추가 by yonghw 20200212
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
				//json은 제외 by yonghw 20200210
				//--시작-- Json 원문 필드 제외시키고, 하위필드를 Facet에 추가한다 by yonghw 20200210
				Fieldconfig.Field jsonField = QDBConfigHandler.getInstance().getConfig(qdb).getFieldconfig(facet.getId());
				if(jsonField != null && 
						jsonField.getDataType().equals(QubeCore.DataType.JSON.name())) {
					//동적 추가된 필드들에 Facet 대상 필드가 있으면 추가한다.
					dynamicFieldConfig.entrySet().stream()
					.filter(f->f.getValue().getId().startsWith(facet.getId()))
					.forEach(ff->makeSsdvStateCache(ff.getValue().getId()));
					//facet 설정 추가하기
					continue;
				}
				//--끝--
				if(facet.getDim() == null && facet.getData() != null) {
					//2018-07-03 SortedSetDocValues Reader State 초기화 추가 by ktKim
					makeSsdvStateCache(facet.getId());
				}
			}
			LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher SSDVReaderState Create Complete(Time:" +(System.currentTimeMillis()-ssdvCreateTime)+"ms)");
		}
		
		//이미지설정이 있을 경우 이미지 검색을 위한 준비를 함.
		if(model.getImageConfig() != null && model.getImageConfig().isSetImages()){
			boolean useImgSearchCache = model.getImageConfig().isUseSearchCache();
			
			//색인서버일 경우 cache를 무조건 만들지 않도록 수정
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
		//메모리 정보 출력.
		LoggerEngine.info(String.format(this.qdb+"[%s] QubeSearcher Created, Mem[max: %sKB, total: %sKB, free: %sKB, used: %sKB]"
				,this.indexDir
				,Tool.fcomma(Runtime.getRuntime().maxMemory()/1024)
				,Tool.fcomma(Runtime.getRuntime().totalMemory()/1024)
				,Tool.fcomma(Runtime.getRuntime().freeMemory()/1024)
				,Tool.fcomma((Runtime.getRuntime().totalMemory()-Runtime.getRuntime().freeMemory())/1024)
		));
		
		//ExcutorService 생성
		if(executor == null) {
			try {
				int threadCnt = QubeCore.getMultiThreadCnt(qdb,false);
				LoggerEngine.info(qdb+" QubeSearcher ExcutorService 생성, Pool Size : " + threadCnt);
				executor = Executors.newFixedThreadPool(threadCnt);
			} catch (Exception e) {
				int defaultThreadCnt = 8;
				LoggerEngine.error("Executor 생성 중 MultiThreadCnt 로드 실패로 기본값("+defaultThreadCnt+")으로 pool을 생성합니다." , e);
				executor = Executors.newFixedThreadPool(defaultThreadCnt);
			} 
		}
		
//		LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher 생성 ("+isSearcherCreate+")"
//				+", QueryResultCache("+qrLimit+")"+", DocumentCache("+docLimit+")"+" 생성이 완료되었습니다.");
		LoggerEngine.info(this.qdb + "["+this.indexDir+"] QubeSearcher 생성 ("+isSearcherCreate+"), TaxonomyReader("+isTaxonomyReaderCreate+")"
				+", QueryResultCache("+qrLimit+")"+", DocumentCache("+docLimit+")"+", FacetCache("+facetDocLimit+")"+" 생성이 완료되었습니다.");
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
			LoggerEngine.infoToDebug("색인된 SSDV의 값이 없습니다.", e);
		}
	}
	
	
	/**
	 * Reader에서 Qdb.xml 에 없는 필드들에 대한 Config를 만들어준다.
	 * 순서: 
	 * 1. 색인파일에서 전체 필드목록 추출
	 * 2. xml Config에서 Json Type인 Map<String, Field> 추출
	 * 3. 전체 필드목록에서 xml Config에 속하지 않고, Json Type 필드명으로 시작하는 경우
	 *    Dynamic Config에 추가한다. (xml Config에서 가져온 필드를 Object Copy 후, ID와 DataType만 바꿔쓴다.)
	 * 
	 * @author : yonghw
	 * @throws Exception 
	 * @revisionHistory
	 * 2020. 2. 12. - 
	 */
	private void makeDynamicConfig() throws Exception {
		//1. 전체 leave 를 확인해서 Map에 담는다. Map<String, FieldInfo>
		//.포함
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
		
		//2. 현재는 Json fieldConfig만 확인
		Map<String, Field> staticConfig = 
		QDBConfigHandler.getInstance().getConfig().get(qdb).getFieldconfig();
		
		//FieldType이 Json인 목록을 추린다.
		Map<String, Field> jsonFieldConfig = 
				staticConfig.entrySet().stream()
		.filter(f->f.getValue().getDataType().equals(QubeCore.DataType.JSON.name()))
		.collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		
		//totalMap의 키 값에 없는 필드인 경우
		Iterator<Entry<String, FieldInfo>> itr = totalMap.entrySet().iterator();
		
		//3. reader 필드 순회
		while(itr.hasNext()) {
			Entry<String, FieldInfo> entry = itr.next();
			//indexed fieldName
			String fieldName = entry.getKey();
			FieldInfo fieldInfo = entry.getValue();
			
			/*//필드명이 $로 시작하는경우 Facet
			if(fieldName.indexOf(QDBConst.FACET_FIELD_PREFIX) == 0) {
				//맨 앞 $ 제거
				String facetName = fieldName.substring(1);
				//기존 config에 없으면, JsonConfig에 해당되는지 확인
				if(staticConfig.get(facetName) == null) {
					Optional<Entry<String, Field>> optional =
							jsonFieldConfig.entrySet().stream()
							.filter(f-> facetName.indexOf(f.getKey()) == 0).findAny();
					if(optional.isPresent()) {
						Facet facet = new Facet();
						//현재는 facet id만 셋팅
						facet.setId(facetName);
						dynamicFacetConfig.put(facetName, facet);
					} else {
						//예외처리(?)
					}
				}
			}
			//xml Config에 없고, Json Type의 이름으로 시작하는 경우
			else*/ 
			if(staticConfig.get(fieldName) == null) {
				Optional<Entry<String, Field>> optional =
				jsonFieldConfig.entrySet().stream()
				//색인된 필드가 Json 필드명으로 시작하는 경우 ex) "JSON_ARRAY.T_PV".startsWith ("JSON_ARRAY")
				.filter(f-> fieldName.startsWith(f.getKey())).findAny();
				if(optional.isPresent()) {
					//원문 필드를 복사한걸 사용(Deep Copy)
					//option.get().getValue() -> jsonFieldConfig의 Field
					Field f = (Field) ObjectCopy.clone(optional.get().getValue());
					f.setId(fieldName);
					f.setDataType(findJsonType(fieldInfo).name());
					/*DataType dataType = findJsonType(fieldInfo);
					f.setDataType(dataType.name());
					// float 이나 date 형의 analyzer는 white space를 사용 
					if(dataType != DataType.VARCHAR) {
						f.setAnalyzer(QDBConst.AnalyzeType.WHITESPACE.name());
					} 
					*/
					this.dynamicFieldConfig.put(fieldName, f);
				} else {
					//예외처리(?)
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
			LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") close 완료");
		} catch (Exception e) {
			throw new QException(QError.SEARCHER_FAIL_READER_CLOSE, QError.SEARCHER_FAIL_READER_CLOSE_MSG, e);
		} finally { 
			//null 처리에 의한 예외를 막기위해 주석 처리 by jilee 2015-05-26
//			searcher = null;
//			reader = null;
//			directory = null;
			
			//캐쉬 Clear시 예외처리 추가 by jilee 2015-06-17
			try{
				queryResultCache.clear();
				documentCache.clear();
				facetCache.clear();
				ssdvStateCache.clear();	//예외 추가 by ktKim 2018-07-03
				LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") 캐시 Clear 완료");
			}catch(Exception e){
				throw new QException(QError.SEARCHER_FAIL_CLEAR_CACHE, QError.SEARCHER_FAIL_CLEAR_CACHE_MSG+" ( "+qdb+"["+indexDir+"] )", e);
			}
		}
		
		//Executor 종료 
		if(executor != null) {
			if(!executor.isShutdown()) executor.shutdown();
			while(!executor.isTerminated()){
				try {
					executor.awaitTermination(1L, TimeUnit.SECONDS);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					LoggerEngine.error("Executor Terminamtion 대기 중 에러", e);
				}
			}
			executor = null;
			LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") ExecutorService 종료 완료");
		}
		
		LoggerEngine.info(qdb + "["+indexDir+"] Old Searcher(hashcode: "+this.hashCode()+") 가 정상 종료 되었습니다 (TotalSearch : "+getTotalSearchCnt()+" / CurrentSearch : " + getCurrentSearchCnt() +")");
	}
	
	public void warmup() throws Exception {
		QDBModel model = QDBConfigHandler.getInstance().getConfig(qdb);
		//warmup 사용 설정이 되어있을 때 실행 by jilee 2014-12-04
		if(model != null && model.getQdbConfig().isUseWarmup()) {
			int warmupCnt=0, fileWarmupCnt=0;
			//유입된 쿼리로 Warmup
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
			
			//파일에 지정한 쿼리로 Warmup
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
			LoggerEngine.info(qdb+"["+indexDir+"] QDB New Searcher의 초기화(Warmup)가 완료되었습니다."
				+" Cached Memory: "+warmupCnt+"/"+ (warmupQueries != null ? warmupQueries.size() : 0)
				+" Cached File: "+fileWarmupCnt+"/"+(fileWarmupQueries != null ?fileWarmupQueries.size() : 0)
			);
		}else 
			LoggerEngine.info(qdb + "["+indexDir+"] QDB New Searcher의 초기화(Warmup)는 실행 하지 않습니다.");
		
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
			LoggerEngine.info("[AddWarmupQuery] 이미 존재하는 쿼리 입니다. size: " + warmupQueries.size()
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
				//한 줄씩 읽어옴
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
				LoggerEngine.info(qdb + "["+indexDir+"] Warmup 쿼리 파일(내용) 없음 ( 경로: " + warmUpFile + " )" );
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
				LoggerEngine.info(qdb + "["+indexDir+"] Warmup 쿼리 파일 close 실패 ( 경로: " + warmUpFile + " )" );
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
		//Filter 셋팅.
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
	 * 검색 결과 {@link DocListAndSet} 생성
	 * @param query
	 * @param filter
	 * @param sort
	 * @param start
	 * @param rows
	 * @param needScores
	 * @param timeLimit - 0이하는 Timeout 처리 X 
	 * @return {@link DocListAndSet}
	 * @throws QException
	 *  @author jilee
	 * <br/>- WINDOW SIZE로 결과를 생하지 않고 순수 start 기준 rows 갯수 만큼만 생성하도록 변경 2017-06-14
	 */
	public final DocListAndSet search(SearchMode mode, Query query, Filter filter, Sort sort, int start, int rows, boolean needScores, long timeLimit) throws Exception{
		//검색후 취득할 rows 갯수를 계산 
		int maxDocRequested = start + rows;
		if(maxDocRequested > reader.maxDoc()) maxDocRequested = reader.maxDoc();
		//최소값 1로 보정하도록 추가 by jilee 2017-06-26
		if(maxDocRequested <= 0) maxDocRequested = 1; 

		//int supersetMaxDoc= maxDocRequested;

		//WINDOW_SIZE 사용 안하도록 변경 by jilee 2017-06-14
		//QUERY_RESULT_WINDOW_SIZE 단위로 검색결과 취득 (취득할 갯수가 61인 경우 70건 취득)
//		if (maxDocRequested < QueryConst.QUERY_RESULT_WINDOW_SIZE) {
//			supersetMaxDoc = QueryConst.QUERY_RESULT_WINDOW_SIZE;
//		} else {
//			supersetMaxDoc = ((maxDocRequested - 1) / QueryConst.QUERY_RESULT_WINDOW_SIZE + 1) * QueryConst.QUERY_RESULT_WINDOW_SIZE;
//			if (supersetMaxDoc < 0) supersetMaxDoc = maxDocRequested;
//		}
		
		//Collector 셋팅.
		Collector finalCollector = null;
		TopDocsCollector<?> topCollector = null;
		DocSetCollector setCollector = null;
		FacetsCollector facetCollector = null;
		if(mode == SearchMode.LISTNSET || mode == SearchMode.LISTONLY){
			//상위 Row결과를 가져올 Collector 설정
			if(sort == null && !needScores){
				//기본 Score 내림차순 정렬 검색 : 정렬이 없고 Score 노출도 없는 경우
				topCollector = TopScoreDocCollector.create(maxDocRequested);
			}else{
				if(sort == null) sort = Sort.RELEVANCE; //정렬이 없을 경우 
				boolean fillFields = true;
				topCollector = TopFieldCollector.create(sort, maxDocRequested, fillFields, needScores, needScores);
			}
			
			//전체 결과 DocIdSet 요청 여부에따라 설정
			if(mode == SearchMode.LISTNSET){
				//검색 결과 전체 DocIdSet을 생성하는 Collector 추가로 셋팅
				/*setCollector = new DocSetCollector(maxDoc());
				finalCollector = MultiCollector.wrap(topCollector,setCollector);*/
				//docIdSet 사용 기능이 없어 Collection하지 않도록 주석
				finalCollector = topCollector;
			}else{
				finalCollector = topCollector;
			}
		} 
		else if(mode == SearchMode.TOPDOCSONLY) {
			//전체 score를 모두 생성
//			topCollector = TopScoreDocCollector.create(reader.maxDoc());
			//DocIndexOrder로 전체 결과 Collect
			topCollector = TopFieldCollector.create(new Sort(SortField.FIELD_DOC), maxDoc(), false, false, false);
			finalCollector = topCollector;
		}
		else if(mode == SearchMode.LEAFDOCS) {
			//세그먼트별 DocIdSet
			facetCollector = new FacetsCollector();
//			finalCollector = fc;
		} else {
			//검색 결과 전체 DocIdSet만 생성하여 Collector 셋팅
			setCollector = new DocSetCollector(maxDoc());
			finalCollector = setCollector;
		}
		
		//Timeout 설정이 있을 경우 Collector 설정
		if(timeLimit > 0){
			finalCollector = new TimeLimitingCollector(finalCollector, TimeLimitingCollector.getGlobalCounter(), timeLimit);
		}
		//Collector 셋팅 끝
		
		long stime = System.nanoTime();
		search(query, filter, finalCollector);
		
		addWarmupQuery(new WarmUpQuery(query, mode, sort, start, rows, needScores));
		long timeIndexSearch = (System.nanoTime()-stime);
		
		stime = System.nanoTime();
		//Collector에 수집된 결과로 DocListAndSet생성
		DocListAndSet ret = new DocListAndSet();
		
		//LEAFDOCS 추가 by yonghw 20180814
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
			//Top Result가 요구 되는 검색 모드에서는 DocList를 생성해준다.
			
			//2018-07-12 처음부터 검색이 아니라 start 부터 Topdoc에서 꺼내도록 수정 by ktKim
			//TopDocs top = topCollector.topDocs(0, maxDocRequested);
			TopDocs top = topCollector.topDocs(start, maxDocRequested);
			int totalHits = topCollector.getTotalHits(); //총 검색결과 건수
			float maxScore = totalHits > 0 ? top.getMaxScore() : 0.0f; //최대 점수값.
			int nDocsReturned = top.scoreDocs.length; //반환결과 건수

			int ids[] = new int[top.scoreDocs.length];
			float scores[] = needScores ? new float[nDocsReturned] : null;
			Object fieldValues[][] = (topCollector instanceof TopFieldCollector) ? new Object[nDocsReturned][] : null;
			for(int i=0; i<nDocsReturned; i++){
				ScoreDoc doc = top.scoreDocs[i];
				ids[i] = doc.doc;
				if(scores != null) scores[i] = doc.score;
				if(fieldValues != null){
					//정렬에서 사용한 필드 및 값 
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
					//일반 검색은 superSet이 start, rows 수만큼만들어져 캐시 되므로 subset사용 X
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
			//2018-07-12 subset 사용하지 않도록 수정 by ktKim
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
	 * 이미지 검색
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
		
		//계산 시간 변수. 유사도 계산전 준비 시간은 INFO로 출력하도록 한다. 
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
					//이미지검색은 검색결과 전체를 소유하고 있어 subset으로 캐시결과를 줌
					subSet = superSet.subset(start, rows);
					if(subSet != null){
						if(superSet instanceof DocSlice){
							ret.setMatcheDocCnt(((DocSlice)superSet).matches);
							ret.setReturnDocCnt(((DocSlice)subSet).len);
						}
						ret.setDocList(subSet);
						//DocSet은 사용하지 않아 주석
//						ret.setDocSet(docListNSet.docSet);
						return ret;
					}
				}
			}
		}
		
		BufferedImage imgBuf = null;
		try {
			
			/**
			 * TopDocs로 이미지유사도 계산하기 위해 검색
			 */
//			docListNSet = search(SearchMode.TOPDOCSONLY, query, filter, null, start, rows, false, timeLimit);
//			int totalHits =  docListNSet.topDocs.totalHits;
			
			/**
			 * DocSet으로 이미지유사도 계산하기 위해 검색
			 */
			docListNSet = search(SearchMode.SETONLY, query, filter, null, start, rows, false, timeLimit);
			int totalHits =  docListNSet.docSet.size();
			if (key != null && totalHits <= Integer.MAX_VALUE ) {
				queryResultCache.put(key, docListNSet);
			}
			
			docsettime = System.nanoTime() - stime;
			
			//이미지 로드
			imgBuf = ImgUtil.getBufferedImage(imgSrcName);
			loadtime = System.nanoTime()-docsettime-stime;
			
			//이미지 리사이징
			try {
				if (Math.max(imgBuf.getHeight(), imgBuf.getWidth()) > QubeImageBulider.MAX_IMAGE_DIMENSION) {
						imgBuf = ImageUtils.scaleImage(imgBuf, QubeImageBulider.MAX_IMAGE_DIMENSION);
	            }
			} catch(Exception e) {
				throw new QException(QError.PARSER_IMAGE_ERR, QError.PARSER_IMAGE_RESIZE_ERROR, 
							"Image = "+imgSrcName ,e);
			}
			
			LoggerEngine.infoToDebug("\t"+query+"\tDocSet "+Tool.fcomma(totalHits)+"건 유사도 정렬 준비 완료[ms] (DocSet,ImgLoad,ImgScale)\t"+Tool.nanoToMilli(docsettime)+"\t"+Tool.nanoToMilli(loadtime)+"\t"+Tool.nanoToMilli(System.nanoTime()-docsettime-loadtime-stime));
			
			//유사도 계산 및 최종 결과 획득 시작
			DocListAndSet imgResult = comparator.search(imgBuf, imgBinaryField, algorithmId, docListNSet, multiCnt, useSimilarityScore, topRate, msCutline, isPrintDetail);
			
			//null 처리 추가 topDocs 사용x
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
	 * facet 검색
	 * - facet 총 연산 횟수 = facet.query절 갯수 * (facet.field절 갯수 + facet.math절 갯수) 
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
		
		//Facet을 지원하지 않는 QDB일 경우 Error Return
		if( QDBConfigHandler.getInstance().getConfig(qdb).getFacetsConfig() == null){
			throw new QException(QError.PARSER_FACET_ERR, QError.PARSER_QDB_NOT_EXISTS_FACET_MSG);
		}
		FacetsConfig facetsConfig = QubeCore.createFacetsConfig(QDBConfigHandler.getInstance().getConfig(qdb).getFacetsConfig());
		
		//Facet작업이 없는 기능도 빈 결과를 셋팅하기위해 초기에 생성
		List<NamedList<String>> facetGroupResults = new ArrayList<>();
		List<NamedList<String>> facetMathResults = new ArrayList<>();
		List<List<FacetNode>> facetTaxoResults = new ArrayList<>();
		
		/**
		 * 1. facet.field의 분류
		 * - SortedSet, Taxonomy facet연산으로 분류
		 * - math연산은 SortedSet Facet연산시 추가로 같이 진행 됨 (현 Taxo는지원 X)
		 */
		ArrayList<FacetCollate> groupList = new ArrayList<>();
		ArrayList<FacetCollate> taxoList = new ArrayList<>();
		FacetCollate[] groups = null;
		FacetCollate[] taxos = null;
		//taxo list를 별도로 추가하면서 사용 X
		//boolean[] taxoFieldIndex = null;	//Result에 순서에 맞게 넣을수 있도록 변수 추가 by ktKim
		if(collates != null) {
			//taxoFieldIndex = new boolean[collates.length];
			for(int i=0;i < collates.length;i++){
				String field = collates[i].getField();
				//Parser에서 Field유효성을 미리 체크하기 때문에 주석 by jilee 2019-06-17
//				if(qdbFacetConfig.get(field) == null){
//					//Error Msg 추가 할지 여부(Parser에서 Check함)
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
		 * 2. 쿼리수 만큼 Facet연산 시작
		 */
		for(Query query : queries) {
			//검색 대상 Collector로 수집
			FacetsCollector fc = null;
			FacetResultPerType facetResultPerType = null;
			
			/**
			 * 3. SortedSetDocValues의 Facet 검색
			 * - 정의한 각 필드에 대한 Group, Math 연산을 지원
			 * - 
			 */
			if(groups != null || maths != null) {
				/**
				 * 3.1 facet.field, facet.math cache 결과 확인
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
				 * 3.2 cache에 없는 경우 검색 시작 
				 * Cache 호출 여부에 따라 Facet 연산을 할 Field를 Parameter 전달하는 방식이 달라지기 때문에 구분하여 호출
				 * (Facet 연산 시 모든 필드를 넣어 한번에 구하기 위하여 사용)
				 */
				if( (groups != null && cachedGroup == null) 
				|| (maths != null && cachedMath == null) ) {	//Group 또는 Math를 하나라도 타지 않을 경우
					if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("[QubeSearcher] Start create facet by ssdv ...");
					//검색 대상 Collector로 수집
					if(fc == null) {
						long fcTime = 0l;
						fc = new FacetsCollector();
						if(LoggerEngine.isDebugEnabled()) fcTime = System.currentTimeMillis();
						search(query, filter != null ? filter : null, fc);
						if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\tFacetCollector create time : " + (System.currentTimeMillis() - fcTime) + "ms");
					}
					
					/**
					 * group이나 math cache에서 꺼내온 결과는 collate를 null을 입력시켜 Facet연산을 하지 않도록 한다
					 */
					facetResultPerType = sortedSetFacetSearch(queryContainer, fc, cachedGroup != null ? null : groups, cachedMath != null ? null : maths, offset, limit, minCount);
					
					//group 결과 취득
					if(cachedGroup == null) {
						if(facetResultPerType.getGroupFacet().size() > 0) putFacetCache(query, filter != null ? filter : null, groups, offset, limit, minCount, new FacetResultCache(facetResultPerType.getGroupFacet()));
						//ret.setFacetList(facetResultPerType.getGroupFacet());
						for(NamedList<String> facetResult : facetResultPerType.getGroupFacet()) {
							facetGroupResults.add(facetResult);
						}
					}
					
					//math 결과 취득
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
			 * 2. TaxonomyIndex를 사용한 Facet 검색
			 * - 여러 필드를 트리형태로 분류한 색인에서 Facet 검색
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
					//검색 대상 Collector로 수집
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
			 * 최종 Facet 결과 생성(Cache가 적용된 경우에는 로직을 타지 않음)
			 * TaxonomyField가 똑같은 Facet.Field로 들어오기 때문에 구분하기 위하여 사용
			 * [group taxo group(multivalue 4) group]의 경우
			 * 2번째 TaxoField는 제외 하고 순차적으로 꺼내어 최종 GroupFacetField 생성
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
		 * 1. 최상위 children 노드정보 생성
		 */
		List<com.giosis.qube.core.facet.FacetResult> topChildren = facets.getAllDims(1);
		
		/**
		 * 2. 각 children 노드의 하위 children 노드 생성
		 */
		for(com.giosis.qube.core.facet.FacetResult topChild : topChildren){
			int facetLimit = topChild.childCount;
			if(limit <= 0) facetLimit = topChild.childCount;
			
			//연산 시간 계산 추가 by jilee 2019-10-15
			
			//topChild의 하위 children 생성
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
		
		//Facet 관련 field, math에 지정한 필드명이 없는 경우  
		if(groups == null && maths == null) return facetResult;
		
		int groupSize = groups != null ? groups.length : 0;
		int mathSize = maths != null ? maths.length : 0;
		int totalCollateSize = groupSize + mathSize;
		
		//1. Facet.math field 설정
		//ExpandVarchar이고, mathField[i]가 JsonBinaryField이면 ssdv를 사용하지 않으므로 state로드시 제외할수 있도록 
		//JsonBinaryField 여부를 배열에 지정 by yonghw 20180621
		for(int i=0;i<mathSize;i++) {
			if(queryContainer.isExpandVarchar() && queryContainer.getExpandVarchar().isJsonField(maths[i].getField())) {
				maths[i].setExpvarchar(true);
			}else {
				maths[i].setExpvarchar(false);
			}
		}
		
		//2. Facet.field와 Facet.math에 선언된 FacetField에 대한 미리 만들어진 SortedSetDocValueReaderState 를 셋팅
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
		
		//3. SortedSetField Facet 연산(생성과 동시에 Count 연산 진행)
		QubeSortedSetFacet facet = new QubeSortedSetFacet(getQdb(), queryContainer, groups, maths, states, fc, totalCollateSize, executor);
		
		//IndexFieldName에 색인된 모든 Facet 정보 Get
		//4. 계산된 Facet 결과를 정렬 및 Dimension(Facet Label) 정보 생성
		List<QubeFacetResult> results = facet.getAllDims(offset, limit, minCount);
		facetResult.setMultiValueCnt(facet.getMultiValueCounts());
		
//		long spanFacetCalc = System.currentTimeMillis() - (currentTime + spanInit);
//		if(LoggerEngine.isDebugEnabled()) LoggerEngine.debug("\t\tMethod facetCalc Time : " + spanFacetCalc + "ms");
		
		//Group 계산
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
		
		//FacetCollate의 groupNo를 key 로 구성한 map
//		Map<Integer, NamedList<String>> mathGroupMap = new LinkedHashMap<>(); 
		Map<Integer, List<FacetMath>> mathGroupMap = new LinkedHashMap<>();
		
		
		//최종 넣은 데이터 기준으로, 재 집계
		//Math 계산, i 는 groupSize부터 시작
		for(int i = groupSize; i < results.size(); i ++) {
			QubeFacetResult result = results.get(i);
			int mathIndex = i - groupSize;
			
			int nowMathGroupN = maths[mathIndex].getFacetMathGroupNo();
			//map으로부터 math groupNo에 해당하는 namedList를 얻어온다. 
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
						//별도 label 지정 필요x, 결과 취합할때 label 넣을 예정
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
		
		//결과 추가, 위의 그루핑된 결과를 그룹내 정렬하여, namedList로 전달한다.
		ArrayList<NamedList<String>> mathFacet = new ArrayList<>();
		Iterator<Entry<Integer, List<FacetMath>>> itr = mathGroupMap.entrySet().iterator();
		FacetMathSort facetMathSort = queryContainer.getFacet().getFacetMathSort();
		while(itr.hasNext()) {
			Entry<Integer, List<FacetMath>> entry = itr.next();
			List<FacetMath> li = entry.getValue();
			
			FacetMath facetMath = null;
			if(li.size() > 0)
				//묶여있는 라벨의 Type은 같으므로, 첫번째 라벨에서 Datatype을 참고함
				facetMath = li.get(0);
			
			//정렬
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
	 * Facet Cache에서 Facet Search
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
