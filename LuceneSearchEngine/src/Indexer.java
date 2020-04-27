package com.giosis.qube.extend.index;

import java.io.File;
import java.io.IOException;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import com.fasterxml.jackson.core.JsonParseException;
import com.giosis.qube.config.ImageFieldRef;
import com.giosis.qube.config.QDBFieldContext;
import com.giosis.qube.config.QDBModel;
import com.giosis.qube.config.qdb.Dimension;
import com.giosis.qube.config.qdb.Fieldconfig;
import com.giosis.qube.config.qdb.Imageconfig;
import com.giosis.qube.constants.QDBConst;
import com.giosis.qube.constants.QDBConst.IndexType;
import com.giosis.qube.constants.QDBConst.IndexWriteType;
import com.giosis.qube.core.QubeCore;
import com.giosis.qube.core.document.Document;
import com.giosis.qube.core.document.Field;
import com.giosis.qube.core.document.Field.Store;
import com.giosis.qube.core.document.FieldType;
import com.giosis.qube.core.document.FloatPoint;
import com.giosis.qube.core.document.LongPoint;
import com.giosis.qube.core.document.SortedNumericDocValuesField;
import com.giosis.qube.core.document.SortedSetDocValuesField;
import com.giosis.qube.core.document.StoredField;
import com.giosis.qube.core.facet.FacetField;
import com.giosis.qube.core.facet.FacetsConfig;
import com.giosis.qube.core.facet.sortedset.SortedSetDocValuesFacetField;
import com.giosis.qube.core.facet.taxonomy.TaxonomyWriter;
import com.giosis.qube.core.index.IndexOptions;
import com.giosis.qube.core.index.IndexWriter;
import com.giosis.qube.core.index.IndexWriterConfig.OpenMode;
import com.giosis.qube.core.index.Term;
import com.giosis.qube.core.util.BytesRef;
import com.giosis.qube.core.util.NumericUtils;
import com.giosis.qube.exception.QError;
import com.giosis.qube.exception.QException;
import com.giosis.qube.extend.index.ConcurrentIndexingCounter.IndexingCounter;
import com.giosis.qube.extend.index.QubeJsonParser.Token;
import com.giosis.qube.logger.LoggerEngine;
import com.giosis.qube.util.FileUtil;
import com.giosis.qube.util.SymbolMap;
import com.giosis.qube.util.TimeStamp;
import com.giosis.qube.util.Tool;

/**
 * @since Qube2.0
 * @author jilee - Create 2016-12-23
 *
 */
public abstract class QubeIndexer extends QubeCore {
	// Single 색인시 스레드번호 지정 상수
	public static final int SINGLE_INDEXER_NUMBER = 0;
	/*
	 * 이미지 색인에서 쓰는 객체 선언
	 */
	public static final int LAP_INDEX_CNT = 10000;
	public static final int LAP_DELETE_CNT = 1000;

	// 분할 Select 카운트 변수
	private static final int MAX_SELECT_CNT = 10000;

	protected int indexerNumber, sequence;
	protected String logPrefix;
	protected boolean allowClose;
	protected volatile boolean stopIndex;
	protected QDBModel qdbModel;
	protected String workQdb;
	protected IndexType type;
	protected IndexWriteType writeType;
	protected IndexWriter writer;
	protected String workIndexPath;
	protected IndexResult indexResult;
	protected IndexingCounter c;

	/**
	 * fieldContext, fieldInstance : Document생성시 재사용하여 쓰는 Instance 객체. FieldContext는
	 * Indexer마다 복제되고 Field 정보와 데이터, FieldInstance는 색인 Field를 맵으로 저장하고 있다
	 */
	protected Map<String, QDBFieldContext> fieldContext;
	protected Map<String, Field> fieldInstance;
	protected List<String> fieldKeyList;

	/**
	 * facetContext : facetConfig로 생성된 Map으로 QDBModel에서 바로 사용하고 ThreadSafe하지 않으므로
	 * 읽기만 한다. facetKeyList : 2차원 정렬된 Facet Key List
	 **/
	protected Map<String, Map<String, List<Dimension>>> facetContext;
	protected List<String> facetKeyList;
	protected Map<String, List<String>> facetDimKeyList;

	/**
	 * 이미지 색인 Config
	 */
	protected Map<String, ImageFieldRef> imgFieldContext;

	protected Document doc; // document도 재사용 하도록 수정 (테스트 진행) 색인속도와 메모리(GC Newing Call 횟수 체크후 결과 주석에 넣기)

	// 2017-11-07 Qube2.0 Facet을 위한 TaxonomyWirter, FacetsConfig 추가 by ktKim
	protected TaxonomyWriter taxWriter;
	protected FacetsConfig fConfig;
	protected ArrayList<String> hierarchiFacetData;

	// json config에서 facetconfig를 변화시켰는지 여부 by yonghw 20200210
	private boolean isFacetDirty = false;

	public abstract void prepareIndex() throws Exception;

	public abstract IndexResult runIndex() throws Exception;

	public abstract void stopIndex() throws Exception;

	public abstract void close() throws Exception;

	public QubeIndexer(int indexerNumber) {
		this.indexerNumber = indexerNumber;
	}

	/**
	 * QubeIndexer 초기화. 새로운 QDB 색인 시에도 초기화하여 사용 가능
	 * 
	 * @param qdbConfig
	 * @param type
	 * @param wtype
	 * @param shareWriter
	 */
	protected void init(int sequence, String workIndexPath, QDBModel qdbModel, IndexType type, IndexWriteType wtype,
			IndexWriter shareWriter, TaxonomyWriter shareTaxWriter, Map<String, QDBFieldContext> fieldContext,
			boolean noMerge) throws Exception {
		this.sequence = sequence;
		this.workIndexPath = workIndexPath;
		this.qdbModel = qdbModel;
		if (qdbModel != null) {
			this.workQdb = qdbModel.getQdbConfig().getId();
		}
		this.type = type;
		this.writeType = wtype;
		this.doc = new Document();
		this.fieldContext = fieldContext;

		// 알파벳으로 정렬된 FieldKeyList 구성
		this.fieldKeyList = new ArrayList<>();
		fieldKeyList.addAll(fieldContext.keySet());
		Collections.sort(fieldKeyList);

		this.fieldInstance = makeFieldInstance(fieldContext, qdbModel.getQdbConfig().isUseTermvector());

		// Facet 및 Facet>Dim 키 정렬 및 FacetKeyList 구성
		this.facetContext = qdbModel.getFacetConfig();
		this.facetKeyList = new ArrayList<>();
		this.facetDimKeyList = new HashMap<>();
		if (facetContext != null) {
			// <Facet>수 만큼 생성
			for (String facetId : facetContext.keySet()) {
				this.facetKeyList.add(facetId);
				// <dim> or <data> 키 리스트를 정렬
				List<String> dimKeyList = new ArrayList<>();
				dimKeyList.addAll(facetContext.get(facetId).keySet());
				Collections.sort(dimKeyList);
				facetDimKeyList.put(facetId, dimKeyList);
			}
			Collections.sort(this.facetKeyList);
		}

		// 이미지 색인용 Mapping 설정 로드.
		Imageconfig imageConfig = qdbModel.getImageConfig();
		if (imageConfig != null && imageConfig.isSetImages()) {
			// 이미지 색인용 Mapping 설정 로드.
			this.imgFieldContext = qdbModel.getImageFieldContext();
		}

		this.indexResult = new IndexResult(indexerNumber);
		this.c = ConcurrentIndexingCounter.getInstance(workQdb); // 병렬인덱서들의 통합 색인카운터

		this.logPrefix = LoggerEngine.INDEX_LOG_PREFIX + this.workQdb + "\t\t[T"
				+ (this.indexerNumber > SINGLE_INDEXER_NUMBER ? this.indexerNumber : "") + "] ";

		if (shareWriter != null) {
			this.allowClose = false;// 공유 Writer를 쓸 경우 Indexer에서 닫을 수 없도록 한다.
			// sharewriter가 Set될 경우는 공유된 디렉토리에 색인을 한다.
			this.writer = shareWriter;
			if (shareTaxWriter != null) {
				this.taxWriter = shareTaxWriter;
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
				// createFacetsConfig(qdbModel.getFacetConfig());
			}
		} else {
			// 공유된 Writer가 없고 전체 색인 일때 색인할 Directory를 비운다.
			this.allowClose = true;
			if (this.type == IndexType.FULL) {
				if (!FileUtil.isExist(this.workIndexPath)) {
					FileUtil.mkdirs(this.workIndexPath);
				}
				FileUtil.deleteFiles(new File(this.workIndexPath));
			}

			// Indexer가 독립된 디렉토리에 색인시 적용하게 된다.
			// 로그 폴더에 색인 기록을 저장하도록 변경 by jilee 2016-02-02
			String indexLogPath = QubeCore.getQdbIndexLogPath(this.qdbModel.getQdbConfig());
			String logFileName = indexLogPath + File.separator + type + "-" + wtype + "-" + this.sequence + "-"
					+ this.indexerNumber + ".log";
			this.writer = openQdbIndexWriter(this.workIndexPath, logFileName, this.qdbModel.getQdbConfig(), type,
					this.type == IndexType.FULL ? OpenMode.CREATE : OpenMode.CREATE_OR_APPEND,
					this.type == IndexType.FULL ? true : false, noMerge);

			// QDBConfig에 Facet생성 정보가 있다면 TaxonomyWriter를 생성한다.
			if (qdbModel.getFacetConfig() != null) {
				taxWriter = openQdbTaxonomyWriter(this.workIndexPath, this.qdbModel.getQdbConfig());
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
			}
		}
	}

	/**
	 * 주어진 fieldContext > Value에 셋팅된 값을 fieldInstance에 주입하여 Document Write <br/>
	 * * 참고 : Indexer에 fieldContext를 재사용하여 쓰지만 다른 fieldContext를 만들어 사용할 기능에 대비해
	 * fieldContext를 파라미터로 받아서 색인하도록 구현함. <br/>
	 * 색인 속도 향상 위키 참고 https://wiki.apache.org/lucene-java/ImproveIndexingSpeed
	 * setDocValByFieldType 함수 추가 by yonghw 20191224
	 * 
	 * @author jilee - 2018-12-12 VARCHAR 타입의 기본값 설정 추가
	 * @throws IOException
	 */
	protected void writeToIndex(Map<String, QDBFieldContext> extFieldContext) throws IOException {

		String pkId = null;
		String pkValue = null;
		Map<String, QDBFieldContext> nowFieldContext = extFieldContext;
		if (nowFieldContext == null)
			nowFieldContext = this.fieldContext;
		Iterator<String> fieldKey = nowFieldContext.keySet().iterator();
		while (fieldKey.hasNext()) {
			String key = fieldKey.next();

			QDBFieldContext fieldInfo = fieldContext.get(key);
			String id = fieldInfo.getId();
			DataType dataType = DataType.valueOf(fieldInfo.getDataType());

			String value = fieldInfo.getValue();
			byte[] binaryValue = fieldInfo.getBinaryValue();

			Field curField = (Field) fieldInstance.get(id);
			Field storedField = (Field) fieldInstance.get(FIELD_PREFIX_STORE + id);
			Field sortedField = (Field) fieldInstance.get(FIELD_PREFIX_SORT + id);

			boolean numeric = setDocValByFieldType(fieldInfo, id, dataType, curField, storedField, sortedField, value,
					binaryValue);

			// PK 필드일경우.
			if (fieldInfo.getUsePk().equalsIgnoreCase("true")) {
				pkId = id;
				pkValue = value;
				// 숫자형 PK필드일 경우에만 PK용 색인 필드 문서에 추가
				if (numeric) {
					Field pkField = (Field) fieldInstance.get(FIELD_PREFIX_PK + id);
					pkField.setStringValue(pkValue);
					doc.add(pkField);
				}
			}

		}

		/**
		 * 2017-11-08 Facet Field 생성 by ktKim FacetField에 공백, 또는 Null 값을 지원하지 않기 때문에 미리
		 * Field생성 후 데이터를 넣지 못하고 Write할때마다 데이터 확인 후 FacetField 생성 EDIT : 2018-01-02
		 * SortedDocValue 사용 할 수 있도록 추가 by ktKim
		 */
		if (facetContext != null && this.facetKeyList != null) {
			Iterator<String> iterFacetKey = facetKeyList.iterator();
			// <Facet>수 만큼 생성
			while (iterFacetKey.hasNext()) {
				// for(String indexFieldName : facetContext.keySet()){
				String facetKey = iterFacetKey.next();

				// --시작-- Json 원문 필드 제외시킴 by yonghw 20200210
				Fieldconfig.Field jsonField = qdbModel.getFieldconfig(facetKey);
				if (jsonField != null && jsonField.getDataType().equals(QubeCore.DataType.JSON.name()))
					continue;
				// --끝--

				// <dim> or <data> 만큼의 FacetField 생성
				Map<String, List<Dimension>> dimentions = facetContext.get(facetKey);
				List<String> dimKeyList = facetDimKeyList.get(facetKey);
				if (dimentions != null && dimKeyList != null) {
					Iterator<String> iterDimKey = dimKeyList.iterator();
					while (iterDimKey.hasNext()) {
						// for(String dimKey : dimentions.keySet()){
						// List<Dimension> dimData = facetContext.get(indexFieldName).get(dimName);
						String dimKey = iterDimKey.next();
						List<Dimension> dimData = dimentions.get(dimKey);
						/**
						 * Lucene 6.3에서 Facet 사용 시 한가지의 Facet Field안에 여러 Field를 사용할 수 가능한데
						 * TaxonomyFacet의 경우 색인 시 TaxonomyFacet 구조 상 Ordinal을 Update 해 주는데 다중 Facet 구조에서
						 * 해결 불가능 하여 1필드 1Value Facet의 경우 SortedSetDocValue Field 사용
						 */
						// <data> 일 경우
						if (dimData.size() == 1) {
							String dataId = dimData.get(0).getId();
							String dataRefField = dimData.get(0).getRefField();
							// Facet에 사용하는 필드명의 Data를 FacetId로 Document에 추가
							if (!dataRefField.equalsIgnoreCase("NONE")) {
								// <data>일 경우에는 SortedDocValue로 생성하도록 변경`
								/*
								 * Field field = new FacetField(facetData.get(0).getId(),
								 * nowFieldContext.get(facetData.get(0).getId()).getValue()); doc.add(field);
								 */
								QDBFieldContext fiConx = nowFieldContext.get(dataRefField);
								String value = fiConx.getValue();
								value = value != null ? value.trim() : "";
								if (value.isEmpty()) {
									String dataType = fiConx.getDataType();
									if (DataType.valueOf(dataType).getValue() < DataType.BINARY.getValue())
										value = QDBConst.UNSUPPORTED_FACET_VALUE_NUMERIC;
									else
										value = QDBConst.UNSUPPORTED_FACET_VALUE_STRING;
								}
								Field field = new SortedSetDocValuesFacetField(dataId, value);
								doc.add(field);
							}
						} else {
							// <dim>의 경우
							hierarchiFacetData = new ArrayList<>();
							for (int i = 0; i < dimData.size(); i++) {
								// String dataId = facetData.get(i).getId();
								// 실제 사용되는 field의 값을 계층데이터리스트에 추가
								String dataRefField = dimData.get(i).getRefField();
								if (!dataRefField.equalsIgnoreCase("NONE")) {
									QDBFieldContext fiConx = nowFieldContext.get(dataRefField);
									String value = fiConx.getValue();
									// 계층데이터에는 기본값을 사용하지 않도록 처리
									value = value != null ? value.trim() : "";
									if (value.isEmpty()) {
										String dataType = fiConx.getDataType();
										if (DataType.valueOf(dataType).getValue() < DataType.BINARY.getValue())
											value = QDBConst.UNSUPPORTED_FACET_VALUE_NUMERIC;
										else
											value = QDBConst.UNSUPPORTED_FACET_VALUE_STRING;
									}
									hierarchiFacetData.add(value);
								} else {
									// 참조 데이터가 하나라도 누락된 Facet설정은 필드추가를 하지 않도록 한다.
									break;
								}
							}

							if (hierarchiFacetData.size() == dimData.size()) {
								Field field = new FacetField(dimKey,
										hierarchiFacetData.toArray(new String[hierarchiFacetData.size()]));
								doc.add(field);
							}
						}
					}
				}
			}
		}

		try {
			if (type == IndexType.FULL) {
//				System.out.println(doc);
				// TaxonomiWriter Facet 분기 추가 by ktKim
				if (taxWriter == null) {
					writer.addDocument(doc);
				} else {
					writer.addDocument(fConfig.build(taxWriter, doc));
				}
			} else if (type == IndexType.APPEND) {
				if (pkId != null && pkValue != null) {
					if (taxWriter == null) {
						writer.updateDocument(new Term(pkId, pkValue), doc);
					} else {
						writer.updateDocument(new Term(pkId, pkValue), fConfig.build(taxWriter, doc));
					}

				}
			}

			// 작업중인 Indexer의 색인완료 카운트 증가 및 로그출력.
			this.indexResult.totalIndexCnt += 1;
			if (this.indexResult.totalIndexCnt % (LAP_INDEX_CNT) == 0) {
				LoggerEngine.info(
						logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt) + " Data Read And Indexed"
								+ " / binary direct = " + Tool.fcomma(this.indexResult.totalDirectBinCnt) + ", skip = "
								+ Tool.fcomma(this.indexResult.totalSkipBinCnt) + " / lap = "
								+ Tool.fcomma(System.currentTimeMillis() - this.indexResult.lapStartTime) + "ms");
				this.indexResult.lapStartTime = System.currentTimeMillis();
			}

			// 전체 색인 총 카운트 증가 및 로그출력.
			c.indexingCountPlus();
			int indexCnt = c.count();
			if (indexCnt % LAP_INDEX_CNT == 0) {
				LoggerEngine.info((new StringBuilder()).append(LoggerEngine.INDEX_LOG_PREFIX + this.workQdb)
						.append(" [Total] document ").append(Tool.fcomma(indexCnt)).append(" indexed")
						.append(" / binary direct = ").append(Tool.fcomma(c.directBinCount())).append(", skip = ")
						.append(Tool.fcomma(c.failCount())).append(" / lap = ").append(Tool.fcomma(c.lapTime()))
						.append("ms / elapsed = ").append(Tool.fcomma(c.totalTime())).append("ms / mem total= ")
						.append(Tool.fcomma(Runtime.getRuntime().totalMemory() / (1024 * 1024))).append("MB, free= ")
						.append(Tool.fcomma(Runtime.getRuntime().freeMemory() / (1024 * 1024))).append("MB, used= ")
						.append(Tool.fcomma((Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory())
								/ (1024 * 1024)))
						.append("MB").toString());
				c.lapTimeInit(); // lapTime 초기화.
			}

		} catch (Exception e) {
			// 색인 에러 Document 출력.
			if (doc != null) {
				LoggerEngine.errorToDebug(logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt)
						+ " 건 색인 후 발생한 문제의 Document");
				nowFieldContext.forEach((key, context) -> {
					LoggerEngine.errorToDebug("\t" + key + "[" + context.getAnalyzer() + ","
							+ context.getAnalyzerOption() + "] " + context.getValue());
				});
//				doc.getFields().forEach(field -> {
//					LoggerEngine.errorToDebug("\t"+field.name()+":"+field.stringValue());
//				});
			}

			throw e;
		} finally {
			// facetConfig 초기화
			if (isFacetDirty)
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
			doc.clear();
		}
	}

	/**
	 * 필드에 값을 추가하고, 숫자 여부를 반환한다.
	 * 
	 * @author : yonghw
	 * @throws IOException
	 * @revisionHistory 2019. 12. 23. -
	 */
	private boolean setDocValByFieldType(QDBFieldContext fieldInfo, String id, DataType dataType, Field curField,
			Field storedField, Field sortedField, String value, byte[] binaryValue) throws IOException {

		// 숫자로 추가되지 않는 경우를 체크
		boolean numeric = true;

		switch (dataType) {
		case INTEGER: {
			int conValue = QDBConst.DEF_FIELD_VALUE_INT;
			try {
				conValue = Integer.valueOf(value);
			} catch (NumberFormatException e) {
				// Ignore Exception
			}
			curField.setIntValue(conValue);
			if (storedField != null)
				storedField.setIntValue(conValue);
			if (sortedField != null)
				sortedField.setLongValue(conValue);
			break;
		}
		case FLOAT: {
			float conValue = QDBConst.DEF_FIELD_VALUE_FLOAT;
			try {
				conValue = Float.valueOf(value);
			} catch (NumberFormatException e) {
				// Ignore Exception
			}
			curField.setFloatValue(conValue);
			if (storedField != null)
				storedField.setFloatValue(conValue);
			// Numeric 필드는 자동으로 정렬이 가능한지 테스트 후 ValueSeting 추가
			if (sortedField != null)
				sortedField.setLongValue(NumericUtils.floatToSortableInt(conValue));
			break;
		}
		case LONG: {
			long conValue = QDBConst.DEF_FIELD_VALUE_LONG;
			try {
				conValue = Long.valueOf(value);
			} catch (NumberFormatException e) {
				// Ignore Exception
			}
			curField.setLongValue(conValue);
			if (storedField != null)
				storedField.setLongValue(conValue);
			// Numeric 필드는 자동으로 정렬이 가능한지 테스트 후 ValueSeting 추가
			if (sortedField != null)
				sortedField.setLongValue(conValue);
			break;
		}
		case DOUBLE: {
			double conValue = QDBConst.DEF_FIELD_VALUE_DOUBLE;
			try {
				conValue = Double.valueOf(value);
			} catch (NumberFormatException e) {
				// Ignore Exception
			}
			curField.setDoubleValue(conValue);
			if (storedField != null)
				storedField.setDoubleValue(conValue);
			// Numeric 필드는 자동으로 정렬이 가능한지 테스트 후 ValueSeting 추가
			if (sortedField != null)
				sortedField.setLongValue(NumericUtils.doubleToSortableLong(conValue));
			break;
		}
		case DATE: {
			long conValue = QDBConst.DEF_FIELD_VALUE_LONG;
			try {
				conValue = TimeStamp.convertDateToLong(value);
			} catch (Exception e) {
				// Ignore Exception
			}
			curField.setLongValue(conValue);
			if (storedField != null)
				storedField.setLongValue(conValue);
			// Numeric 필드는 자동으로 정렬이 가능한지 테스트 후 ValueSeting 추가
			if (sortedField != null)
				sortedField.setLongValue(NumericUtils.doubleToSortableLong(conValue));
			break;
		}
		default: {
			numeric = false;
			switch (dataType) {
			case VARCHAR:
			case EXPVARCHAR:
			case JSON:
				// VARCHAR Type 인 경우 해당 value trim을 해준다...by smh
				curField.setStringValue(value.trim());
				break;
			case BINARY:
				curField.setBytesValue(binaryValue == null ? BytesRef.EMPTY_BYTES : binaryValue);
				break;
			default:
				curField.setStringValue(value.trim());
				break;
			}
			if (sortedField != null) {
				if (binaryValue == null) {
					// 2018-06-28 Sort시 대소문자 구분 없이 정렬하기 위해(또는 전, 반각 구분없이) SymbolMap 적용 by ktKim
					String symbolValue = SymbolMap.apply(value.trim());
					binaryValue = symbolValue.getBytes("UTF-8");
				}
				sortedField.setBytesValue(binaryValue);
			}
			break;
		}
		}

		doc.add(curField); // 문서에 추가

		if (numeric) {
			// 숫자형 필드일 경우
			// 노출용 필드 설정이 있을 시 문서에 추가
			if (storedField != null)
				doc.add(storedField);
		} else {
			// String binary 필드일경우.
		}

		// 정렬용 필드 설정이 있을 시 문서에 추가
		if (sortedField != null) {
			doc.add(sortedField);
		}

		// Json형 일 때 value 파싱하여 색인필드 추가 by yonghw 20191224 (원문은 위에서 추가됬고, 파싱필드 추가)
		if (dataType.name().equals(DataType.JSON.name())) {
			if (value != null) {
				QubeJsonParser jsonParser = QubeJsonContent.createParser(value);
				parsingObject(fieldInfo, id, jsonParser);
			}
		}
		return numeric;
	}

	/**
	 * Json String을 파싱해서 색인필드로 추가하기 위한 함수 입니다. 각 기호 "{", "}"를 parser의 nextToken()할 떄
	 * "START_OBJECT", "END_OBJECT"로 봅니다. "START_OBJECT", "START_ARRAY" 는 재귀적으로
	 * 동작하며, 그 외에 VALUE에서는 색인 필드를 추가하는 동작을 합니다.
	 * 
	 * @author : yonghw
	 */
	private void parsingObject(QDBFieldContext fieldInfo, String key, QubeJsonParser parser)
			throws JsonParseException, IOException {
		while (parser.nextToken() != null && (parser.currentToken() != Token.END_OBJECT)) {
//			System.out.println(parser.getCurrentToken() + " // " + parser.getCurrentName());
			String cName = parser.currentName();
			String nowKey = "";
			// 필드명 확장, 대문자로 확장
			if (cName != null)
				nowKey = key + FIELD_SPLITTER + cName.toUpperCase().trim().replaceAll("\\s+", " ");
			else
				nowKey = key;

			switch (parser.currentToken()) {
			case START_OBJECT:
				parsingObject(fieldInfo, nowKey, parser);
				break;
			case START_ARRAY:
				parsingArray(fieldInfo, nowKey, parser);
				break;
			case VALUE_NUMBER: {
				String value = parser.textOrNull();
				if (value == null)
					value = "0";
				addJson(fieldInfo, nowKey, value, DataType.FLOAT, false);
				break;
			}
			case VALUE_STRING:
			case VALUE_BOOLEAN:
			case VALUE_NULL: {
				String value = parser.textOrNull();
				if (value == null)
					value = "";
				DataType dataType = DataType.VARCHAR;
				try {
					// 날짜 Type인지 체크 (yyyy-MM-dd HH:mm:ss) 이면 (yyyyMMddHHmmss) 로 변환한다.
					Date d = extendsFormat.parse(value);
					value = format.format(d);
					dataType = DataType.DATE;
				} catch (ParseException p) {
				}
				addJson(fieldInfo, nowKey, value, dataType, false);
				break;
			}
			default:
				break;
			}
		}
//		System.out.println(parser.getCurrentToken() + " /		/ " + parser.getCurrentName());
	}

	/**
	 * @author : yonghw
	 */
	private void addJson(QDBFieldContext fieldInfo, String key, String value, DataType dataType, boolean isMultiValue)
			throws IOException {
		String store = fieldInfo.getStore();
		String sort = fieldInfo.getSort();
		// String facet = fieldInfo.getStore();
		final String NOT_USE_PARAM = "";

		// 원문 저장 여부 설정. FL절에 사용가능 유무
		Store stored = store.equalsIgnoreCase("ON") ? Store.YES : Store.NO;
		// 정렬용 DocValues 생성 여부
		boolean sorted = sort.equalsIgnoreCase("ON");

		// 필드 생성사용하기 전, 공백 여부 추가
		/*
		 * if(Tool.isSpace(key)) { QException e = new
		 * QException(QError.INDEX_JSON_PARSE_SPACE_FAIL,
		 * QError.INDEX_JSON_PARSE_SPACE_FAIL_MSG, key); e.logError(); throw e; }
		 */

		// Facet 추가
		if (qdbModel.getFacetConfig() != null
				// json 원문필드의 id로 확인
				&& qdbModel.getFacetConfig().containsKey(fieldInfo.getId())) {
			String facetValue = value != null ? value.trim() : "";
			if (facetValue.isEmpty()) {
				// 숫자형이면
				if (dataType.getValue() < DataType.BINARY.getValue())
					facetValue = QDBConst.UNSUPPORTED_FACET_VALUE_NUMERIC;
				else
					facetValue = QDBConst.UNSUPPORTED_FACET_VALUE_STRING;
			}
			// json 필드로 facet 추가
			doc.add(new SortedSetDocValuesFacetField(key, facetValue));
			// config에 추가
			this.isFacetDirty = true;
			fConfig.setIndexFieldName(key, QDBConst.FACET_FIELD_PREFIX + key);
			if (isMultiValue) {
//				System.out.println("ismultiValued:" + key );
				fConfig.setMultiValued(key, true);
			}
		}

		/*
		 * if(!fieldInstance.containsKey(key)) { Json 데이터의 stored, sorted 속성은 Json Type의
		 * 필드값을 따라가고 isPk, useTermVector는 false 처리
		 * 
		 * addUseAnalField(key, dataType, fieldInstance, stored, sorted, false,
		 * NOT_USE_PARAM, false); }
		 */

		Field curField = null, storedField = null, sortedField = null;

		switch (dataType) {
		case FLOAT: {
			curField = new FloatPoint(key, QDBConst.DEF_FIELD_VALUE_FLOAT);
			if (stored == Store.YES)
				storedField = new StoredField(key, QDBConst.DEF_FIELD_VALUE_FLOAT);
			if (sorted)
				sortedField = new SortedNumericDocValuesField(key,
						NumericUtils.floatToSortableInt(QDBConst.DEF_FIELD_VALUE_FLOAT));
			break;
		}
		case DATE: {
			curField = new LongPoint(key, QDBConst.DEF_FIELD_VALUE_LONG);
			if (stored == Store.YES)
				storedField = new StoredField(key, QDBConst.DEF_FIELD_VALUE_LONG);
			if (sorted)
				sortedField = new SortedNumericDocValuesField(key, QDBConst.DEF_FIELD_VALUE_LONG);
			break;
		}
		case VARCHAR: {
			FieldType type = new FieldType();

			// 두 인덱스 옵션의 검색 속도 및 색인 크기 비교해보고 결정하기
			// type.setIndexOptions(IndexOptions.DOCS_AND_FREQS_AND_POSITIONS_AND_OFFSETS);
			type.setIndexOptions(IndexOptions.DOCS_AND_FREQS_AND_POSITIONS);

			type.setTokenized(true);
			type.setOmitNorms(true);
			// Json은 TermVectors 사용 X by yonghw
			type.setStoreTermVectors(false);
			type.setStoreTermVectorPositions(false);
			type.setStoreTermVectorOffsets(false);
			type.setStoreTermVectorPayloads(false);
			type.setStored(stored == Store.YES ? true : false);
			curField = new Field(key, QDBConst.DEF_FIELD_VALUE_VARCHAR, type);
			// multi value의 sorting을 위해 SortedDocValues -> SortedSetDocValuesField 를 사용 by
			// yonghw
			if (sorted)
				sortedField = new SortedSetDocValuesField(key, new BytesRef(QDBConst.DEF_FIELD_VALUE_VARCHAR));
			break;
		}
		default: {
			throw new QException(QError.INDEX_JSON_SUPPORT_FAIL, QError.INDEX_JSON_SUPPORT_FAIL_MSG);
		}
		}

//		curField.setTokenStream(jsonAnalyzerMap.get(QDBConst.AnalyzeType.WHITESPACE.name()).tokenStream(fieldName, text));

		setDocValByFieldType(fieldInfo
		/*
		 * 최종 세팅 정보에서는 key 값이 필요가 없음, 함수 호출을 위해 파라미터를 지정해야하기 때문에 빈값을(NOT_USE_PARAM)
		 * 넘겨줍니다. by yonghw
		 */
				, NOT_USE_PARAM, dataType, curField, storedField, sortedField
				// numeric 설정 기본 값 = true
				, value, null);

	}

	private void setMap(Map<String, MultiJsonData> m, DataType dataType, String key, String value) {
		if (m.containsKey(key)) {
			m.get(key).addValue(value);
		} else {
			m.put(key, new MultiJsonData(dataType, value));
		}
	}

	// start array에서 시작
	private void parsingArray(QDBFieldContext fieldInfo, String key, QubeJsonParser parser)
			throws JsonParseException, IOException {

		Map<String, MultiJsonData> map = new HashMap<>();

		while (parser.nextToken() != Token.END_ARRAY) {
			String cName = parser.currentName();
			String nowKey = "";
			if (cName != null)
				nowKey = key + FIELD_SPLITTER + cName.toUpperCase().trim().replaceAll("\\s+", " ");
			else
				nowKey = key;

			switch (parser.currentToken()) {
			case START_OBJECT:
				parsingArrayObject(fieldInfo, nowKey, parser, map);
				break;
			case START_ARRAY:
				parsingArray(fieldInfo, nowKey, parser);
				break;
			case VALUE_NUMBER: {
				String value = parser.textOrNull();
				if (value == null)
					value = "0";
				setMap(map, DataType.FLOAT, nowKey, value);
				// System.out.println("key:" + nowKey + " value:" + parser.getText());
				break;
			}
			case VALUE_STRING:
			case VALUE_BOOLEAN:
			case VALUE_NULL: {
				String value = parser.textOrNull();
				if (value == null)
					value = "";

				DataType dataType = DataType.VARCHAR;
				try {
					// 날짜 Type인지 체크 (yyyy-MM-dd HH:mm:ss) 이면 (yyyyMMddHHmmss) 로 변환한다.
					Date d = extendsFormat.parse(value);
					value = format.format(d);
					dataType = DataType.DATE;
				} catch (ParseException p) {
				}
				setMap(map, dataType, nowKey, value);
				break;
			}
			default:
				break;
			}
		}
		/*
		 * map.forEach((k,v) -> { System.out.println("[Array]key:" + k );
		 * v.stream().forEach(o-> System.out.println("[Array Multi Value]" + o)); } );
		 */
		/*
		 * map.forEach((k,v) -> { String type = v.getDataType();
		 * v.getValueList().forEach(t-> { addJson(doc, fieldInfo, key, t, type,
		 * fieldInstance); }); });
		 */

		addMultiValue(map, fieldInfo);

		// Array가 끝난 시점의 map의 key, value 정보 확인 후 필드정보를 셋팅한다.
//		System.out.println(parser.getCurrentToken() + " // " + parser.getCurrentName());
	}

	private void addMultiValue(Map<String, MultiJsonData> map, QDBFieldContext fieldInfo) throws IOException {

		Iterator<Entry<String, MultiJsonData>> itr = map.entrySet().iterator();

		while (itr.hasNext()) {
			Entry<String, MultiJsonData> entry = itr.next();
			String key = entry.getKey();
			MultiJsonData value = entry.getValue();
			for (String v : value.getValueList()) {
				addJson(fieldInfo, key, v, value.getDataType(), true);
			}
		}

	}

	// Array에서 파생된 Object정보
	private void parsingArrayObject(QDBFieldContext fieldInfo, String key, QubeJsonParser parser,
			Map<String, MultiJsonData> map) throws JsonParseException, IOException {
		// END_OBJECT가
		while (parser.nextToken() != Token.END_OBJECT) {
			String cName = parser.currentName();
			String nowKey = "";

			if (cName != null)
				nowKey = key + FIELD_SPLITTER + cName.toUpperCase().trim().replaceAll("\\s+", " ");
			else
				nowKey = key;

			switch (parser.currentToken()) {
			case START_OBJECT:
				parsingArrayObject(fieldInfo, nowKey, parser, map);
				break;
			case START_ARRAY:
				parsingArray(fieldInfo, nowKey, parser);
				break;
			case VALUE_NUMBER: {
				String value = parser.textOrNull();
				if (value == null)
					value = "0";
				setMap(map, DataType.FLOAT, nowKey, value);
				// System.out.println("key:" + nowKey + " value:" + parser.getText());
				break;
			}
			case VALUE_STRING:
			case VALUE_BOOLEAN:
			case VALUE_NULL: {
				String value = parser.textOrNull();
				if (value == null)
					value = "";

				DataType dataType = DataType.VARCHAR;
				try {
					// 날짜 Type인지 체크 (yyyy-MM-dd HH:mm:ss) 이면 (yyyyMMddHHmmss) 로 변환한다.
					Date d = extendsFormat.parse(value);
					value = format.format(d);
					dataType = DataType.DATE;
				} catch (ParseException p) {
				}
				setMap(map, dataType, nowKey, value);
				break;
			}
			default:
				break;
			}
		}
	}

	protected void deleteFromIndex(Map<String, QDBFieldContext> extFieldContext) {
		String pkID = null;
		String pkValue = null;

		Map<String, QDBFieldContext> nowFieldContext = extFieldContext;
		if (nowFieldContext == null)
			nowFieldContext = this.fieldContext;

		try {
			Iterator<String> fieldKey = nowFieldContext.keySet().iterator();
			while (fieldKey.hasNext()) {
				String key = fieldKey.next();

				QDBFieldContext fieldInfo = nowFieldContext.get(key);
				String pk = fieldInfo.getUsePk();
				String id = fieldInfo.getId();
				String value = fieldInfo.getValue();
				if (pk.equalsIgnoreCase("TRUE")) {
					pkID = id;
					pkValue = value;
					break;
				}
			}

			if (pkID != null && pkValue != null) {
				// 셋팅된 PK 값으로 색인에서 삭제 실행.
				writer.deleteDocuments(new Term(pkID, pkValue));

				// 캐시에서도 제거.
				// cache.removeCacheOne(pkValue);

				// 인덱스 캐시 제거로 인한 주석처리 by tcpark 2016-12-06
				// cache.removeCacheOne(workQDB, pkValue);

				// 작업중인 ImageIndexer의 색인 삭제 완료 카운트 증가 및 로그출력.
				this.indexResult.totalIndexCnt += 1;
				if (this.indexResult.totalIndexCnt % (LAP_DELETE_CNT) == 0) {
					LoggerEngine.info(logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt)
							+ " deleted " + Tool.fcomma(this.indexResult.totalFailCnt) + " failed");

					// 랩타임 마다 잠시 슬립하도록 추가. (해당 스레드가 자원 독점이 sleep을 통해 해제 되는지 테스트 하기 위함)
					// try{ Thread.sleep(5l);}catch(InterruptedException e){}
				}

				// 전체 색인 총 삭제 카운트 증가 및 로그출력.
				c.indexingCountPlus();
				int indexCnt = c.count();
				if (indexCnt % LAP_DELETE_CNT == 0) {
					LoggerEngine.info((new StringBuilder()).append(LoggerEngine.INDEX_LOG_PREFIX + this.workQdb)
							.append(" [Total] document ").append(Tool.fcomma(indexCnt)).append(" deleted ")
							.append(Tool.fcomma(c.failCount())).append(" failed ").append("/ lap = ")
							.append(Tool.fcomma(c.lapTime())).append("ms / elapsed = ")
							.append(Tool.fcomma(c.totalTime())).append("ms / mem total= ")
							.append(Tool.fcomma(Runtime.getRuntime().totalMemory() / (1024 * 1024)))
							.append("MB, free= ").append(Tool.fcomma(Runtime.getRuntime().freeMemory() / (1024 * 1024)))
							.append("MB, used= ")
							.append(Tool.fcomma((Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory())
									/ (1024 * 1024)))
							.append("MB").toString());
					c.lapTimeInit(); // lapTime 초기화.
				}
			} else {
				this.indexResult.totalFailCnt += 1;
				c.indexingFailCountPlus();
				LoggerEngine.warn(logPrefix + writeType + " fail. PK Field가 아니거나 PK Field Value가 잘못되어서 삭제할 수 없습니다. : "
						+ pkID + ", " + pkValue);
			}
		} catch (Exception e) {
			// Document 색인 실패시 실패카운트 증가 및 에러로그 출력
			this.indexResult.totalFailCnt += 1;
			c.indexingFailCountPlus();
			LoggerEngine.error(logPrefix + writeType + " fail [PK: " + pkValue, e);
		}
	}

	public int getIndexerNumber() {
		return indexerNumber;
	}

	public void setIndexerNumber(int indexerNumber) {
		this.indexerNumber = indexerNumber;
	}

	public String getWorkIndexPath() {
		return workIndexPath;
	}

	public void setWorkIndexPath(String workIndexPath) {
		this.workIndexPath = workIndexPath;
	}
}
