package dk.itu.openjmltest.api;

import java.io.File;
import java.io.IOException;
import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import com.sun.tools.javac.tree.JCTree;


public class TestOpenJMLAPI {
	
	
	private static API api;

	/**
	 * Setup API 
	 */	
	@BeforeClass 
	public static void setupOpenJML() throws IOException {

		api = new API();		
	
	}

	
	@Test
	public void testCallOpenJMLAPI() throws IOException 
	{
	
		String dir = System.getProperty("user.dir") + System.getProperty("file.separator");		   
		File file = new File(dir+"src/ForAll.txt");
		JmlCompilationUnit f =  api.parseSingleFile(file);
		//Object tree = f.clone();
		JCTree tree = f.getTree();
		// do we have a *real* ast here ?
		// if so figure out:
		// 1) how to traverse the tree
		// 2) print it out in a more tree structure fashion		
		
		//api.prettyPrint(ast, likeSource)
		
		System.out.println("f:");
		System.out.println(f);

		System.out.println("tree:");
		System.out.println(tree);
		
//		Assert.assertNull(f);
//		Assert.assertNull(tree);

		}	
	
	
	
}
