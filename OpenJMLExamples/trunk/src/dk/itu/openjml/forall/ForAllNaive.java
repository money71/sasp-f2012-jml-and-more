package dk.itu.openjml.forall;

import org.jmlspecs.openjml.API;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

public class ForAllNaive {
	
	/**
	 * 
	 * @param tree JML AST containing a \forall expression
	 * @return Java code that asserts the given \forall expression
	 */
	public static String generateForAll(JmlCompilationUnit tree) {
		
		return "";
	}
	
	/**
	 * 
	 * @param tree JML AST containing a \forall expression
	 * @return True if the \forall expression holds, false otherwise
	 */
	public static boolean assertForAll(JmlCompilationUnit tree) {
		
		return true;
	}
	
	public static void main(String[] args) throws java.io.IOException{
		try {
			API openjmlApi = new API();
			JmlCompilationUnit tree = openjmlApi.parseSingleFile(new java.io.File(args[0]));
			assertForAll(tree);
			generateForAll(tree);
		} catch (NullPointerException e) {
			throw new java.io.IOException("Need path to a .java file as argument.");
		}
	}
}
