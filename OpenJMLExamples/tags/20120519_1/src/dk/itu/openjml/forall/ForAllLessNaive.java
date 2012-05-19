package dk.itu.openjml.forall;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.ListBuffer;

public class ForAllLessNaive {
	
	/**
	 * Converts a JmlQuantifiedExpr into executable code which is returned as a String
	 * @param tree JML AST containing a \forall expression
	 * @return Java code that asserts the given \forall expression
	 */
	public static String generateForAll(JmlQuantifiedExpr tree) {
		
		// Storing the code
		String generated = "static boolean JmlRac$AssertForAll(){\n\t";
		int lBrackCount = 0;
		
		// FIXME: What about parameters?
		
		List<String> forLoops = getForLoop(tree.decls, tree.range);
		List<String> predicates = getPredicate(tree.value);
		
		// Adding for loops
		for(String s: forLoops){
			generated += s + "\n";
			lBrackCount++;
		}
				
		// Adding predicate assertion
		generated += "true){\nif(!(";
		for(String s: predicates){
			generated += "(" + s + ")" + " && ";
		}
		
		// Finishing syntax
		generated += "true)){\n\treturn false;\n}\n}";
		while(lBrackCount > 0){
			generated += "\n}";
			lBrackCount--;
		}
		
		// Default return
		generated += "\nreturn true;\n}";
		return generated;
	}
	
	private static List<String> getForLoop(ListBuffer<JCVariableDecl> e, JCExpression f){
		List<String> forLoops = new ArrayList<String>();
		
		// TODO: Ideally, we will replace this by a for(Object i: Iterable){ or something
		for(JCVariableDecl d: e){
			String type = d.type.toString();
			String id = d.name.toString();
//			forLoops.add("for(" + type + " " + id + ": " + getSet(id, f) + "){\n");
//			forLoops.add("for(" + type + " " + id + " = "+ getLowerBounds(id, f) + "; " // Initialize
//					+ id + "<=" + getUpperBounds(id, f) + "; " // Guard
//					+ id + "++){\n"); // Step ahead
		}		
		return forLoops;
	}
	
	private static String getLowerBounds(String id, JCExpression e){
		
		if(e instanceof JCBinary && e.toString().contains(id)){
			
			// Check both expressions
			String l = getLowerBounds(id, ((JCBinary) e).lhs);
			String r = getLowerBounds(id, ((JCBinary) e).rhs);
			
			// We're looking for the smaller one
			return new Integer(l) > new Integer(r) ? r : l;
		} else if(e.type.toString() == "int"){
			return e.toString();
		} else {
			return "Integer.MAX_VALUE";
		}
	}
	
	private static String getUpperBounds(String identifier, JCExpression e){
		
		// Default return value if no range is defined properly
		return "Integer.MAX_VALUE";
	}
	
	private static List<String> getRangeExpression(JCExpression e){
		List<String> ranges = new ArrayList<String>();
		
		// We just take the whole expression as one assertion
		ranges.add(e.toString());
		return ranges;
	}
	
	private static List<String> getPredicate(JCExpression e){
		List<String> predicates = new ArrayList<String>();
		
		// We just take the whole expression as one assertion
		predicates.add(e.toString());
		return predicates;
	}
}
