package dk.itu.openjml.forall;

import java.util.ArrayList;
import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;

public class ForAllSetBased {
	/*
	 * This is a first attempt to formulate a class as outlined in
	 * http://code.google.com/p/sasp-f2012-jml-and-more/wiki/ApproachTowardsQuantifiers
	 * 
	 * FIXME: The class is not pure but all the methods are. Should instead the class be pure?
	 * 
	 * TODO: Implement generateCheck - basic call structure.
	 * TODO: Implement generateDeclaration - figure out which race variables need to be declared.
	 * TODO: Implement generateForLoop - build a (nested)for-loop of the form {{{for(T t: S)...}}}
	 * TODO: Implement generatePredicate - generate a proper predicate check - maybe replace with something more general?
	 * TODO: Implement evaluateRange - probably the hardest one here, generate a set (collection) at runtime of values to iterate over.
	 * TODO: How to formulate a range-expression that can be evaluated at runtime?
	 */
	
	// These are the allowed types of a declaration
	private static final String[] ALLOWED_TYPES = {"boolean", "char", "int", "Object"};
	
	// Simple replacement
	private static /*@ pure @*/ String getObjectType(String primitive){
		switch(primitive){
			case "boolean": return "Boolean";
			case "char": return "Character";
			case "int": return "Integer";
			// The following datatypes are not supported right now
			case "long":
			case "double":
			case "float": return null;
		}
		return primitive;
	}
	
	// TODO: Write specs
	public static /*@ pure @*/ String generateCheck(JmlQuantifiedExpr e){
		// TODO: Should this return a whole method body or just a body?
		return generateForLoop(e);
	}
	
	// TODO: Write specs
	public static /*@ pure @*/ <T> List<T> evaluateRange(JCExpression e){
		return new ArrayList<T>();
	}
	
	// TODO: Write specs
	private static /*@ pure @*/ String generateForLoop(JmlQuantifiedExpr e){
		String gen = "for(" 
				+ generateDeclaration(e.decls.next())
				+ ": dk.itu.openjml.forall.ForAllSetBased.evaluateRange()){\n";
		if(e.decls){
			// TODO: generateForLoop();
		} else {
			gen += generatePredicate(e.value);
		}
		gen += "}\n";
		return gen;
	}
	
	
	// TODO: Write specs
	private static /*@ pure @*/ String generateDeclaration(JCVariableDecl e){
		return "";
	}
	
	// TODO: Write specs
	private static /*@ pure @*/ String generatePredicate(JCExpression e){
		return "";
	}
}