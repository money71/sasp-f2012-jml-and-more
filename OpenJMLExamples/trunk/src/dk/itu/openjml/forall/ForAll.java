package dk.itu.openjml.forall;

import java.util.List;

import org.jmlspecs.openjml.JmlTree.JmlQuantifiedExpr;

import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.ListBuffer;

import dk.itu.openjml.quantifiers.QRange;

/**
 * This is the class that generates code to  evaluate JML \forall 
 * expressions using QRange to interpret a range expression and 
 * Range and Interval to build a list of numbers that represents
 * all valid values for a variable. 
 */
public class ForAll {

	String generated;
	JmlQuantifiedExpr expr;
	
	final static String LOOP_START = "for(";
	final static String LOOP_SEPARATOR = " : ";
	final static String LOOP_END = ")";
	
	final static String BLOCK_START = "{";
	final static String BLOCK_END = "}";
	
	final static String SEPARATOR = " ";
	final static String STATEMENT_END = ";";
	
	// TODO: We need a proper assertion check that gives some info #9
	final static String ASSERT = "assert";
	
	/**
	 * Constructs a string that holds code to evaluate the 
	 * given expression
	 * @param e The JmlQuantifiedExpr to generate evaluation code for
	 */
	//@ assignable generated, expr;
	public ForAll(JmlQuantifiedExpr e){
		generated = "";
		expr = e;
		generate();
	}
	
	/**
	 * Generates the code. If the quantified expression is not executable,
	 * the incident gets reported and an empty statement (;) is produced.
	 */
	protected void generate(){
		try{
			addLoops(getDeclarations());
		} catch (QRange.NotExecutableQuantifiedExpr e){
			// TODO: Report properly! #10
			add(STATEMENT_END);
		}
	}
	
	/**
	 * Adds nested loops to the generated code until no more declarations
	 * are left. Then the predicate statement is added to the most inner
	 * loop body.
	 * @param list
	 * @throws QRange.NotExecutableQuantifiedExpr
	 */
	//@ assignable s;
	protected void addLoops(/*@ non_null @*/ List<JCVariableDecl> decls) throws QRange.NotExecutableQuantifiedExpr {
		if(!decls.isEmpty()){
			JCVariableDecl d = decls.get(0);
			decls.remove(0); // FIXME: Doesn't work! #11
			
			// Add the loop header
			addLoopHeader(d.name.toString(), d.type.toString());	

			// Add the next inner loop
			add(BLOCK_START); // {
			addLoops(decls); // <body>
			add(BLOCK_END); // }
			
		} else {
			addPredicate();
		}
		
	}
	
	/**
	 * @return A list containing all JCVariableDecl objects of the expression tree
	 */
	protected List<JCVariableDecl> getDeclarations(){
		return expr.decls.toList();
	}
	
	/**
	 * Adds a string to the generated code.
	 * @param s String that should be added to the code
	 */
	//@ requires generated != null;
	//@ assignable s;
	//@ ensures generated.startsWith(\old(generated));
	protected void add(/*@ non_null @*/ String s){
		generated += s;
	}
	
	/**
	 * Adds a for-loop head to the generated code.
	 * @param type Type of the variable
	 * @param var Variable name
	 * @throws QRange.NotExecutableQuantifiedExpr if QRange cannot evaluate a proper range for the variable
	 */
	//@ requires generated != null;
	//@ assignable s;
	//@ ensures generated.startsWith(\old(generated));
	protected void addLoopHeader(/*@ non_null @*/ String type, /*@ non_null @*/ String var) throws QRange.NotExecutableQuantifiedExpr{
		
		// Generate code that generates an interval object during runtime
		QRange range = QRange.compute(expr.range, var);
		
		add(LOOP_START); // for(
		add(type);	// int
		add(SEPARATOR);
		add(var); // i
		add(LOOP_SEPARATOR); // :
		add(range.translate()); // [i_0, ..., i_n]
		add(LOOP_END); // )
	}
	
	/**
	 * Adds a predicate check to the code.
	 */
	//@ requires generated != null;
	//@ assignable s;
	//@ ensures generated.startsWith(\old(generated));
	//@ ensures generated.endsWith(STATEMEND_END);
	protected void addPredicate(){
		// TODO: #9
		add(ASSERT);
		add(SEPARATOR);
		add(expr.value.toString());
		add(STATEMENT_END);
	}
	
	/**
	 * @return Code that evaluates this for all expression during RAC.
	 */
	public /*@ pure @*/ String translate(){
		return generated;
	}
	
	public /*@ pure @*/ String toString(){
		return translate();
	}
}
