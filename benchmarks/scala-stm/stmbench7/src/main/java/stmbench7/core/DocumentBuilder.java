package stmbench7.core;

import stmbench7.Parameters;
import stmbench7.annotations.Immutable;
import stmbench7.backend.BackendFactory;
import stmbench7.backend.IdPool;
import stmbench7.backend.Index;

/**
 * Used to create and destroy document elements while
 * maintaining the consistency of the data structure
 * and the indexes.
 */
@Immutable
public class DocumentBuilder extends DesignObjBuilder {

	private final IdPool idPool;
	private final Index<String,Document> documentTitleIndex;
	
	public DocumentBuilder(Index<String,Document> documentTitleIndex) {
		this.documentTitleIndex = documentTitleIndex;
		idPool = BackendFactory.instance.createIdPool(Parameters.MaxCompParts);
	}
	
	public Document createAndRegisterDocument(int compositePartId) throws OperationFailedException {
		int docId = idPool.getId();
		String docTitle = "Composite Part #" + compositePartId;
		String docText = createText(Parameters.DocumentSize, 
					      "I am the documentation for composite part #" + compositePartId + "\n");

		Document documentation = designObjFactory.createDocument(docId, docTitle, docText);
		documentTitleIndex.put(docTitle, documentation);
		
		return documentation;
	}

	public void unregisterAndRecycleDocument(Document document) {
		document.setPart(null);
		documentTitleIndex.remove(document.getTitle());
		idPool.putUnusedId(document.getDocumentId());
	}
}
