import java.io.IOException;
import org.jmlspecs.openjml.API;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;


public class TestOpenJMLAPI {
	
	
	private static API api;

	/**
	 * Setup API
	 * 
	 * Will be perform before each test case 
	 */	
	@Before 
	public void setupSearchEngine() throws IOException {

		api = new API();		
	
	}

	
	@Test
	public void testCallOpenJMLAPI() throws IOException 
	{
	
//		public void indexFile(String fileName) throws IOException {
//
//			// We assume file is in UTF-8 text format.
//			BufferedReader r = new BufferedReader(new InputStreamReader(new FileInputStream(fileName), "UTF-8"));
//
//			int count = 0;
//
//			while (true) {
//				String s = r.readLine();
//				if (s == null) break; // no more lines
//				lines.add(s);
//
//				//add word to map and line
//				addIndex(s, count);
//				count++;
//
//			}
//
//		}
//		
//		
//		String dir = System.getProperty("user.dir") + System.getProperty("file.separator");		   
//        engine = new FileSE();
//        engine.indexFile(dir+"src/pellekrogholt/algorithm_assignment_5/shells.txt");
//		
//		File file = 
//		api.parseSingleFile(file);
//		
////		String result = "<p><b>Query string</b>: the  <b>Lines</b>: 0, 1, 2, </p>";
////		Assert.assertEquals(engine.search("the"), result);		

		}	
	
	
	
}
