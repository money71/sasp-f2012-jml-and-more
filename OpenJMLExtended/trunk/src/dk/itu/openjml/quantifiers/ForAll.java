package dk.itu.openjml.quantifiers;

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
	
	private final static String LOOP_START = "for(";
	private final static String LOOP_SEPARATOR = " : ";
	private final static String LOOP_END = ")";
	
	private final static String BLOCK_START = "{";
	private final static String BLOCK_END = "}";
	
	private final static String SEPARATOR = " ";
	private final static /*@ spec_public @*/ String STATEMENT_END = ";";
	
	// NOTE: #9
	private final static String ASSERT = "assert";
	
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
			// NOTE: #10
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
	//@ assignable decls;
	protected void addLoops(/*@ non_null @*/ ListBuffer<JCVariableDecl> decls) throws QRange.NotExecutableQuantifiedExpr {
		//if(decls != null && !decls.isEmpty()){
		if(!decls.isEmpty()){
			JCVariableDecl d = decls.next(); // same as next / poll
			// Add the loop header
			addLoopHeader(d);	
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
	// FIXME: it assumes toList() doesn't do anything in ListBuffer at this point
	// - can we say anything more in terms om jml specs... #21 
	protected /*@ pure @*/ ListBuffer<JCVariableDecl> getDeclarations(){
		// expr.decls is a ListBuffer then turned into a javac List
		return expr.decls;
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
	//@ assignable decl;
	//@ ensures generated.startsWith(\old(generated));
	protected void addLoopHeader(/*@ non_null @*/ JCVariableDecl decl) throws QRange.NotExecutableQuantifiedExpr{
		
		// Generate code that generates an interval object during runtime
		// - decl.name.toString() should work(TM) though we had odd cases with decl.var being *null*  
		QRange range = QRange.compute(expr.range, decl.name.toString());
		
		add(LOOP_START); // for(
		add(decl.toString()); // type var e.g. int i
		add(LOOP_SEPARATOR); // :
		add(range.translate()); // [i_0, ..., i_n]
		add(LOOP_END); // )
	}
	
	/**
	 * Adds a predicate check to the code.
	 */
	//@ requires generated != null;
	//@ ensures generated.startsWith(\old(generated));
	//@ ensures generated.endsWith(";");
	protected void addPredicate(){
		// NOTE: #9
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
