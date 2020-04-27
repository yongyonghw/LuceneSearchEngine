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
	// Single ���ν� �������ȣ ���� ���
	public static final int SINGLE_INDEXER_NUMBER = 0;
	/*
	 * �̹��� ���ο��� ���� ��ü ����
	 */
	public static final int LAP_INDEX_CNT = 10000;
	public static final int LAP_DELETE_CNT = 1000;

	// ���� Select ī��Ʈ ����
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
	 * fieldContext, fieldInstance : Document������ �����Ͽ� ���� Instance ��ü. FieldContext��
	 * Indexer���� �����ǰ� Field ������ ������, FieldInstance�� ���� Field�� ������ �����ϰ� �ִ�
	 */
	protected Map<String, QDBFieldContext> fieldContext;
	protected Map<String, Field> fieldInstance;
	protected List<String> fieldKeyList;

	/**
	 * facetContext : facetConfig�� ������ Map���� QDBModel���� �ٷ� ����ϰ� ThreadSafe���� �����Ƿ�
	 * �б⸸ �Ѵ�. facetKeyList : 2���� ���ĵ� Facet Key List
	 **/
	protected Map<String, Map<String, List<Dimension>>> facetContext;
	protected List<String> facetKeyList;
	protected Map<String, List<String>> facetDimKeyList;

	/**
	 * �̹��� ���� Config
	 */
	protected Map<String, ImageFieldRef> imgFieldContext;

	protected Document doc; // document�� ���� �ϵ��� ���� (�׽�Ʈ ����) ���μӵ��� �޸�(GC Newing Call Ƚ�� üũ�� ��� �ּ��� �ֱ�)

	// 2017-11-07 Qube2.0 Facet�� ���� TaxonomyWirter, FacetsConfig �߰� by ktKim
	protected TaxonomyWriter taxWriter;
	protected FacetsConfig fConfig;
	protected ArrayList<String> hierarchiFacetData;

	// json config���� facetconfig�� ��ȭ���״��� ���� by yonghw 20200210
	private boolean isFacetDirty = false;

	public abstract void prepareIndex() throws Exception;

	public abstract IndexResult runIndex() throws Exception;

	public abstract void stopIndex() throws Exception;

	public abstract void close() throws Exception;

	public QubeIndexer(int indexerNumber) {
		this.indexerNumber = indexerNumber;
	}

	/**
	 * QubeIndexer �ʱ�ȭ. ���ο� QDB ���� �ÿ��� �ʱ�ȭ�Ͽ� ��� ����
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

		// ���ĺ����� ���ĵ� FieldKeyList ����
		this.fieldKeyList = new ArrayList<>();
		fieldKeyList.addAll(fieldContext.keySet());
		Collections.sort(fieldKeyList);

		this.fieldInstance = makeFieldInstance(fieldContext, qdbModel.getQdbConfig().isUseTermvector());

		// Facet �� Facet>Dim Ű ���� �� FacetKeyList ����
		this.facetContext = qdbModel.getFacetConfig();
		this.facetKeyList = new ArrayList<>();
		this.facetDimKeyList = new HashMap<>();
		if (facetContext != null) {
			// <Facet>�� ��ŭ ����
			for (String facetId : facetContext.keySet()) {
				this.facetKeyList.add(facetId);
				// <dim> or <data> Ű ����Ʈ�� ����
				List<String> dimKeyList = new ArrayList<>();
				dimKeyList.addAll(facetContext.get(facetId).keySet());
				Collections.sort(dimKeyList);
				facetDimKeyList.put(facetId, dimKeyList);
			}
			Collections.sort(this.facetKeyList);
		}

		// �̹��� ���ο� Mapping ���� �ε�.
		Imageconfig imageConfig = qdbModel.getImageConfig();
		if (imageConfig != null && imageConfig.isSetImages()) {
			// �̹��� ���ο� Mapping ���� �ε�.
			this.imgFieldContext = qdbModel.getImageFieldContext();
		}

		this.indexResult = new IndexResult(indexerNumber);
		this.c = ConcurrentIndexingCounter.getInstance(workQdb); // �����ε������� ���� ����ī����

		this.logPrefix = LoggerEngine.INDEX_LOG_PREFIX + this.workQdb + "\t\t[T"
				+ (this.indexerNumber > SINGLE_INDEXER_NUMBER ? this.indexerNumber : "") + "] ";

		if (shareWriter != null) {
			this.allowClose = false;// ���� Writer�� �� ��� Indexer���� ���� �� ������ �Ѵ�.
			// sharewriter�� Set�� ���� ������ ���丮�� ������ �Ѵ�.
			this.writer = shareWriter;
			if (shareTaxWriter != null) {
				this.taxWriter = shareTaxWriter;
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
				// createFacetsConfig(qdbModel.getFacetConfig());
			}
		} else {
			// ������ Writer�� ���� ��ü ���� �϶� ������ Directory�� ����.
			this.allowClose = true;
			if (this.type == IndexType.FULL) {
				if (!FileUtil.isExist(this.workIndexPath)) {
					FileUtil.mkdirs(this.workIndexPath);
				}
				FileUtil.deleteFiles(new File(this.workIndexPath));
			}

			// Indexer�� ������ ���丮�� ���ν� �����ϰ� �ȴ�.
			// �α� ������ ���� ����� �����ϵ��� ���� by jilee 2016-02-02
			String indexLogPath = QubeCore.getQdbIndexLogPath(this.qdbModel.getQdbConfig());
			String logFileName = indexLogPath + File.separator + type + "-" + wtype + "-" + this.sequence + "-"
					+ this.indexerNumber + ".log";
			this.writer = openQdbIndexWriter(this.workIndexPath, logFileName, this.qdbModel.getQdbConfig(), type,
					this.type == IndexType.FULL ? OpenMode.CREATE : OpenMode.CREATE_OR_APPEND,
					this.type == IndexType.FULL ? true : false, noMerge);

			// QDBConfig�� Facet���� ������ �ִٸ� TaxonomyWriter�� �����Ѵ�.
			if (qdbModel.getFacetConfig() != null) {
				taxWriter = openQdbTaxonomyWriter(this.workIndexPath, this.qdbModel.getQdbConfig());
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
			}
		}
	}

	/**
	 * �־��� fieldContext > Value�� ���õ� ���� fieldInstance�� �����Ͽ� Document Write <br/>
	 * * ���� : Indexer�� fieldContext�� �����Ͽ� ������ �ٸ� fieldContext�� ����� ����� ��ɿ� �����
	 * fieldContext�� �Ķ���ͷ� �޾Ƽ� �����ϵ��� ������. <br/>
	 * ���� �ӵ� ��� ��Ű ���� https://wiki.apache.org/lucene-java/ImproveIndexingSpeed
	 * setDocValByFieldType �Լ� �߰� by yonghw 20191224
	 * 
	 * @author jilee - 2018-12-12 VARCHAR Ÿ���� �⺻�� ���� �߰�
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

			// PK �ʵ��ϰ��.
			if (fieldInfo.getUsePk().equalsIgnoreCase("true")) {
				pkId = id;
				pkValue = value;
				// ������ PK�ʵ��� ��쿡�� PK�� ���� �ʵ� ������ �߰�
				if (numeric) {
					Field pkField = (Field) fieldInstance.get(FIELD_PREFIX_PK + id);
					pkField.setStringValue(pkValue);
					doc.add(pkField);
				}
			}

		}

		/**
		 * 2017-11-08 Facet Field ���� by ktKim FacetField�� ����, �Ǵ� Null ���� �������� �ʱ� ������ �̸�
		 * Field���� �� �����͸� ���� ���ϰ� Write�Ҷ����� ������ Ȯ�� �� FacetField ���� EDIT : 2018-01-02
		 * SortedDocValue ��� �� �� �ֵ��� �߰� by ktKim
		 */
		if (facetContext != null && this.facetKeyList != null) {
			Iterator<String> iterFacetKey = facetKeyList.iterator();
			// <Facet>�� ��ŭ ����
			while (iterFacetKey.hasNext()) {
				// for(String indexFieldName : facetContext.keySet()){
				String facetKey = iterFacetKey.next();

				// --����-- Json ���� �ʵ� ���ܽ�Ŵ by yonghw 20200210
				Fieldconfig.Field jsonField = qdbModel.getFieldconfig(facetKey);
				if (jsonField != null && jsonField.getDataType().equals(QubeCore.DataType.JSON.name()))
					continue;
				// --��--

				// <dim> or <data> ��ŭ�� FacetField ����
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
						 * Lucene 6.3���� Facet ��� �� �Ѱ����� Facet Field�ȿ� ���� Field�� ����� �� �����ѵ�
						 * TaxonomyFacet�� ��� ���� �� TaxonomyFacet ���� �� Ordinal�� Update �� �ִµ� ���� Facet ��������
						 * �ذ� �Ұ��� �Ͽ� 1�ʵ� 1Value Facet�� ��� SortedSetDocValue Field ���
						 */
						// <data> �� ���
						if (dimData.size() == 1) {
							String dataId = dimData.get(0).getId();
							String dataRefField = dimData.get(0).getRefField();
							// Facet�� ����ϴ� �ʵ���� Data�� FacetId�� Document�� �߰�
							if (!dataRefField.equalsIgnoreCase("NONE")) {
								// <data>�� ��쿡�� SortedDocValue�� �����ϵ��� ����`
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
							// <dim>�� ���
							hierarchiFacetData = new ArrayList<>();
							for (int i = 0; i < dimData.size(); i++) {
								// String dataId = facetData.get(i).getId();
								// ���� ���Ǵ� field�� ���� ���������͸���Ʈ�� �߰�
								String dataRefField = dimData.get(i).getRefField();
								if (!dataRefField.equalsIgnoreCase("NONE")) {
									QDBFieldContext fiConx = nowFieldContext.get(dataRefField);
									String value = fiConx.getValue();
									// ���������Ϳ��� �⺻���� ������� �ʵ��� ó��
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
									// ���� �����Ͱ� �ϳ��� ������ Facet������ �ʵ��߰��� ���� �ʵ��� �Ѵ�.
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
				// TaxonomiWriter Facet �б� �߰� by ktKim
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

			// �۾����� Indexer�� ���οϷ� ī��Ʈ ���� �� �α����.
			this.indexResult.totalIndexCnt += 1;
			if (this.indexResult.totalIndexCnt % (LAP_INDEX_CNT) == 0) {
				LoggerEngine.info(
						logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt) + " Data Read And Indexed"
								+ " / binary direct = " + Tool.fcomma(this.indexResult.totalDirectBinCnt) + ", skip = "
								+ Tool.fcomma(this.indexResult.totalSkipBinCnt) + " / lap = "
								+ Tool.fcomma(System.currentTimeMillis() - this.indexResult.lapStartTime) + "ms");
				this.indexResult.lapStartTime = System.currentTimeMillis();
			}

			// ��ü ���� �� ī��Ʈ ���� �� �α����.
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
				c.lapTimeInit(); // lapTime �ʱ�ȭ.
			}

		} catch (Exception e) {
			// ���� ���� Document ���.
			if (doc != null) {
				LoggerEngine.errorToDebug(logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt)
						+ " �� ���� �� �߻��� ������ Document");
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
			// facetConfig �ʱ�ȭ
			if (isFacetDirty)
				fConfig = createFacetsConfig(qdbModel.getFacetsConfig());
			doc.clear();
		}
	}

	/**
	 * �ʵ忡 ���� �߰��ϰ�, ���� ���θ� ��ȯ�Ѵ�.
	 * 
	 * @author : yonghw
	 * @throws IOException
	 * @revisionHistory 2019. 12. 23. -
	 */
	private boolean setDocValByFieldType(QDBFieldContext fieldInfo, String id, DataType dataType, Field curField,
			Field storedField, Field sortedField, String value, byte[] binaryValue) throws IOException {

		// ���ڷ� �߰����� �ʴ� ��츦 üũ
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
			// Numeric �ʵ�� �ڵ����� ������ �������� �׽�Ʈ �� ValueSeting �߰�
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
			// Numeric �ʵ�� �ڵ����� ������ �������� �׽�Ʈ �� ValueSeting �߰�
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
			// Numeric �ʵ�� �ڵ����� ������ �������� �׽�Ʈ �� ValueSeting �߰�
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
			// Numeric �ʵ�� �ڵ����� ������ �������� �׽�Ʈ �� ValueSeting �߰�
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
				// VARCHAR Type �� ��� �ش� value trim�� ���ش�...by smh
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
					// 2018-06-28 Sort�� ��ҹ��� ���� ���� �����ϱ� ����(�Ǵ� ��, �ݰ� ���о���) SymbolMap ���� by ktKim
					String symbolValue = SymbolMap.apply(value.trim());
					binaryValue = symbolValue.getBytes("UTF-8");
				}
				sortedField.setBytesValue(binaryValue);
			}
			break;
		}
		}

		doc.add(curField); // ������ �߰�

		if (numeric) {
			// ������ �ʵ��� ���
			// ����� �ʵ� ������ ���� �� ������ �߰�
			if (storedField != null)
				doc.add(storedField);
		} else {
			// String binary �ʵ��ϰ��.
		}

		// ���Ŀ� �ʵ� ������ ���� �� ������ �߰�
		if (sortedField != null) {
			doc.add(sortedField);
		}

		// Json�� �� �� value �Ľ��Ͽ� �����ʵ� �߰� by yonghw 20191224 (������ ������ �߰����, �Ľ��ʵ� �߰�)
		if (dataType.name().equals(DataType.JSON.name())) {
			if (value != null) {
				QubeJsonParser jsonParser = QubeJsonContent.createParser(value);
				parsingObject(fieldInfo, id, jsonParser);
			}
		}
		return numeric;
	}

	/**
	 * Json String�� �Ľ��ؼ� �����ʵ�� �߰��ϱ� ���� �Լ� �Դϴ�. �� ��ȣ "{", "}"�� parser�� nextToken()�� ��
	 * "START_OBJECT", "END_OBJECT"�� ���ϴ�. "START_OBJECT", "START_ARRAY" �� ���������
	 * �����ϸ�, �� �ܿ� VALUE������ ���� �ʵ带 �߰��ϴ� ������ �մϴ�.
	 * 
	 * @author : yonghw
	 */
	private void parsingObject(QDBFieldContext fieldInfo, String key, QubeJsonParser parser)
			throws JsonParseException, IOException {
		while (parser.nextToken() != null && (parser.currentToken() != Token.END_OBJECT)) {
//			System.out.println(parser.getCurrentToken() + " // " + parser.getCurrentName());
			String cName = parser.currentName();
			String nowKey = "";
			// �ʵ�� Ȯ��, �빮�ڷ� Ȯ��
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
					// ��¥ Type���� üũ (yyyy-MM-dd HH:mm:ss) �̸� (yyyyMMddHHmmss) �� ��ȯ�Ѵ�.
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

		// ���� ���� ���� ����. FL���� ��밡�� ����
		Store stored = store.equalsIgnoreCase("ON") ? Store.YES : Store.NO;
		// ���Ŀ� DocValues ���� ����
		boolean sorted = sort.equalsIgnoreCase("ON");

		// �ʵ� ��������ϱ� ��, ���� ���� �߰�
		/*
		 * if(Tool.isSpace(key)) { QException e = new
		 * QException(QError.INDEX_JSON_PARSE_SPACE_FAIL,
		 * QError.INDEX_JSON_PARSE_SPACE_FAIL_MSG, key); e.logError(); throw e; }
		 */

		// Facet �߰�
		if (qdbModel.getFacetConfig() != null
				// json �����ʵ��� id�� Ȯ��
				&& qdbModel.getFacetConfig().containsKey(fieldInfo.getId())) {
			String facetValue = value != null ? value.trim() : "";
			if (facetValue.isEmpty()) {
				// �������̸�
				if (dataType.getValue() < DataType.BINARY.getValue())
					facetValue = QDBConst.UNSUPPORTED_FACET_VALUE_NUMERIC;
				else
					facetValue = QDBConst.UNSUPPORTED_FACET_VALUE_STRING;
			}
			// json �ʵ�� facet �߰�
			doc.add(new SortedSetDocValuesFacetField(key, facetValue));
			// config�� �߰�
			this.isFacetDirty = true;
			fConfig.setIndexFieldName(key, QDBConst.FACET_FIELD_PREFIX + key);
			if (isMultiValue) {
//				System.out.println("ismultiValued:" + key );
				fConfig.setMultiValued(key, true);
			}
		}

		/*
		 * if(!fieldInstance.containsKey(key)) { Json �������� stored, sorted �Ӽ��� Json Type��
		 * �ʵ尪�� ���󰡰� isPk, useTermVector�� false ó��
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

			// �� �ε��� �ɼ��� �˻� �ӵ� �� ���� ũ�� ���غ��� �����ϱ�
			// type.setIndexOptions(IndexOptions.DOCS_AND_FREQS_AND_POSITIONS_AND_OFFSETS);
			type.setIndexOptions(IndexOptions.DOCS_AND_FREQS_AND_POSITIONS);

			type.setTokenized(true);
			type.setOmitNorms(true);
			// Json�� TermVectors ��� X by yonghw
			type.setStoreTermVectors(false);
			type.setStoreTermVectorPositions(false);
			type.setStoreTermVectorOffsets(false);
			type.setStoreTermVectorPayloads(false);
			type.setStored(stored == Store.YES ? true : false);
			curField = new Field(key, QDBConst.DEF_FIELD_VALUE_VARCHAR, type);
			// multi value�� sorting�� ���� SortedDocValues -> SortedSetDocValuesField �� ��� by
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
		 * ���� ���� ���������� key ���� �ʿ䰡 ����, �Լ� ȣ���� ���� �Ķ���͸� �����ؾ��ϱ� ������ ����(NOT_USE_PARAM)
		 * �Ѱ��ݴϴ�. by yonghw
		 */
				, NOT_USE_PARAM, dataType, curField, storedField, sortedField
				// numeric ���� �⺻ �� = true
				, value, null);

	}

	private void setMap(Map<String, MultiJsonData> m, DataType dataType, String key, String value) {
		if (m.containsKey(key)) {
			m.get(key).addValue(value);
		} else {
			m.put(key, new MultiJsonData(dataType, value));
		}
	}

	// start array���� ����
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
					// ��¥ Type���� üũ (yyyy-MM-dd HH:mm:ss) �̸� (yyyyMMddHHmmss) �� ��ȯ�Ѵ�.
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

		// Array�� ���� ������ map�� key, value ���� Ȯ�� �� �ʵ������� �����Ѵ�.
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

	// Array���� �Ļ��� Object����
	private void parsingArrayObject(QDBFieldContext fieldInfo, String key, QubeJsonParser parser,
			Map<String, MultiJsonData> map) throws JsonParseException, IOException {
		// END_OBJECT��
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
					// ��¥ Type���� üũ (yyyy-MM-dd HH:mm:ss) �̸� (yyyyMMddHHmmss) �� ��ȯ�Ѵ�.
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
				// ���õ� PK ������ ���ο��� ���� ����.
				writer.deleteDocuments(new Term(pkID, pkValue));

				// ĳ�ÿ����� ����.
				// cache.removeCacheOne(pkValue);

				// �ε��� ĳ�� ���ŷ� ���� �ּ�ó�� by tcpark 2016-12-06
				// cache.removeCacheOne(workQDB, pkValue);

				// �۾����� ImageIndexer�� ���� ���� �Ϸ� ī��Ʈ ���� �� �α����.
				this.indexResult.totalIndexCnt += 1;
				if (this.indexResult.totalIndexCnt % (LAP_DELETE_CNT) == 0) {
					LoggerEngine.info(logPrefix + "document " + Tool.fcomma(this.indexResult.totalIndexCnt)
							+ " deleted " + Tool.fcomma(this.indexResult.totalFailCnt) + " failed");

					// ��Ÿ�� ���� ��� �����ϵ��� �߰�. (�ش� �����尡 �ڿ� ������ sleep�� ���� ���� �Ǵ��� �׽�Ʈ �ϱ� ����)
					// try{ Thread.sleep(5l);}catch(InterruptedException e){}
				}

				// ��ü ���� �� ���� ī��Ʈ ���� �� �α����.
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
					c.lapTimeInit(); // lapTime �ʱ�ȭ.
				}
			} else {
				this.indexResult.totalFailCnt += 1;
				c.indexingFailCountPlus();
				LoggerEngine.warn(logPrefix + writeType + " fail. PK Field�� �ƴϰų� PK Field Value�� �߸��Ǿ ������ �� �����ϴ�. : "
						+ pkID + ", " + pkValue);
			}
		} catch (Exception e) {
			// Document ���� ���н� ����ī��Ʈ ���� �� �����α� ���
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
