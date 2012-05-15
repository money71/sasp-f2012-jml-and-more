package dk.itu.openjml.quantifiers;

import org.jmlspecs.openjml.JmlTree.JmlBinary;

import com.sun.tools.javac.tree.JCTree.JCBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;

/**
 * Inspired from the QSet class implemented for JML2
 * 
 * This class represents a quantified range over integers.
 * It walks over an expression tree and translate atomic
 * boolean expressions into a set of values. As an atomic
 * boolean expression can only define one margin of a range,
 * the other margin will by default be Integer.MAX_VALUE or
 * respectively Integer.MIN_VALUE. Through operations on
 * sets these "infinite" margins will be reduced to a valid
 * set of ranges which can also have gaps.
 */
public abstract class QRange {
	
	// Conjunction and disjunction
	final static String CON = "&&";
	final static String DIS = "||";
	
	// Implications (FIXME: currently not used)
	final static String RIMP = "==>";
	final static String LIMP = "<==";
	final static String BIMP = "<==>";
	
	// Boolean operators on numbers
	final static String GT = ">";
	final static String GEQ = ">=";
	final static String LT = "<";
	final static String LEQ = "<=";
	final static String EQ = "==";
	final static String NEQ = "!=";
	
	// Branches
	QRange left;
	QRange right;
	
	/**
	 * Returns an instance of QRange that represents a (set of) range(s)
	 * @param e An expression defining the range
	 * @param var A variable for which the range should be computed for
	 * @return A new QRange for the given expression and variable
	 * @throws Exception Thrown if the expression contains logical operations we are not willing or able to process.
	 */
	public static QRange compute(JCExpression e, String var) throws Exception{
		
		// We only want to process binary expressions
		if(e instanceof JCBinary){
			if(hasOperator((JCBinary)e, CON)) { 
				// Conjunction is an intersection
				return new IntersectionQRange((JCBinary)e, var);
				
			} else if(hasOperator((JCBinary)e, DIS)) {
				// Disjunction is a union
				return new UnionQRange((JCBinary)e, var);
				
			} else if(isAtomic((JCBinary)e)){ 
				// Leaf node representing actual range definitions
				return new LeafQRange((JCBinary)e, var);
			} 
			// TODO: Add pure method calls?
		}
		throw new Exception("Cannot execute this statement: " + e.toString()); // FIXME: Do this properly
	}
	
	/**
	 * Build a QRange object that holds QRanges through compute
	 * @param e A JmlBinay expression which describes a range
	 * @param var A variable name for which we want to find the range
	 * @throws Exception If e is not an executable statement
	 */
	public QRange(JCBinary e, String var) throws Exception{
		left = compute(e.lhs, var);
		right = compute(e.rhs, var);
	}
	
	/**
	 * Empty default constructor
	 */
	protected QRange(){
		left = null;
		right = null;
	}
	
	/**
	 * Checks recursively if an expression contains a variable name
	 * @param e The expression tree
	 * @param var The variable name
	 * @return True if e contains var, false otherwise
	 */
	static /*@ pure @*/ boolean containsVar(JCExpression e, String var){
		if(e instanceof JmlBinary){
			return containsVar(((JmlBinary)e).lhs, var) || containsVar(((JmlBinary)e).rhs, var);
		}
		// FIXME: Do this the proper way
		return e.toString().contains(var);
	}
	
	/**
	 * Checks a JmlBinary expression for a given operator
	 * @param e A JmlBinary expression
	 * @param o Some operator
	 * @return True if o is the operator in e
	 */
	static /*@ pure @*/ boolean hasOperator(JCBinary e, String o){
		return getOperator(e).equals(o);
	}
	
	/**
	 * Returns a string which is the operator of a JCBinary expression
	 * @param e A JCBinary expression
	 * @return The operator in e
	 */
	static /*@ pure @*/ String getOperator(JCBinary e){
		// This hurts my eyes!
		String op = e.toString();
		op = op.replace(e.lhs.toString(), "");
		op = op.replace(e.rhs.toString(), "");
		op = op.replace(" ", "");
		return op;
	}
	
	/**
	 * Checks if a JmlBinary expression is an atomic boolean expression
	 * @param e A JmlBinary expression
	 * @return True if e is an atomic boolean expression, false otherwise
	 */
	static /*@ pure @*/ boolean isAtomic(JCBinary e){
		return hasOperator(e, GT) ||
				hasOperator(e, EQ) ||
				hasOperator(e, LT) ||
				hasOperator(e, GEQ) ||
				hasOperator(e, LEQ);
	}
	
	/**
	 * Generates source code from this QRange.
	 * @return Source code building a valid range of integers.
	 */
	abstract public /*@ pure @*/ String translate();
	
	public /*@ pure @*/ String toString(){
		return translate();
	}
	
	/**
	 * @return True if the fields left and right are null
	 */
	public /*@ pure @*/ boolean isLeaf(){
		return left == null && right == null;
	}
}

/**
 * Represents a union of two ranges
 */
class UnionQRange extends QRange {
	
	public UnionQRange(JCBinary e, String var) throws Exception{
		super(e, var);
	}
	
	/**
	 * Generates the code for a union-operation on ranges
	 */
	public /*@ pure @*/ String translate(){
		return "(" + left.translate() + " UNION " + right.translate() + ")";
	}
	
}

/**
 * Represents an intersection of two ranges 
 */
class IntersectionQRange extends QRange {
	
	public IntersectionQRange(JCBinary e, String var) throws Exception{
		super(e, var);
	}
	
	/**
	 * Generates the code for an intersect-operation on ranges
	 */
	public /*@ pure @*/ String translate(){
		return "(" + left.translate() + " INTERSECTION " + right.translate() + ")";
	}
}

/**
 * Represents a range defined through a boolesn expression
 */
class LeafQRange extends QRange {
	
	String var;
	String low;
	String high;
	int ilow;
	int ihigh;
	
	public LeafQRange(JCBinary e, String var) throws Exception{
		// Store the variable name
		this.var = var;
		
		ilow = Integer.MIN_VALUE;
		ihigh = Integer.MAX_VALUE;
		low = "Integer.MIN_VALUE";
		high = "Integer.MAX_VALUE";
		
		String left = e.lhs.toString();
		//String op = e.operator.toString();
		String op = getOperator(e);
		String right = e.rhs.toString();
		
		evaluateExpression(left, op, right);
	}
	
	// TODO: Write specs!
	/**
	 * Evaluates an expression made from three strings, left,
	 * op, right, after these rules:
	 * 
	 * (Note: had to switch rules 1 and 3 and 2 and 4 to guarantee inclusive ranges.)
	 * 
	 * e[l o r] =: 
	 *   r = var && !(l = var) ==> e[l o^(-1) r]
	 * | o = "<=" ==> high = r
	 * | o = ">=" ==> low = r
	 * | o = "<" ==> e[l "<=" (r - 1)]
	 * | o = ">" ==> e[l ">=" (r + 1)]
	 * | o = "!=" ==> low = (r + 1) && high = (r - 1)
	 * | o = "==" ==> low = r && high = r
	 * 
	 * @param left A value or a identifier
	 * @param op A operator
	 * @param right A value or an identifier
	 * @throws Exception if none of the rules apply to this expression
	 */
	private void evaluateExpression(String left, String op, String right) throws Exception{
		
		if(right.contains(var) && !left.contains(var)){
			// Switch left and right part of the expression, change operator orientation
			evaluateExpression(right, changeOrientation(op), left);
			return;
		
		} else if(op.equals(LEQ)){
			// Right is the maximum value
			high = right;
			return;
			
		} else if(op.equals(GEQ)){
			// Right is the minimum value
			low = right;
			return;			
		
		} else if(op.equals(LT)){
			// Replace "i <= x" by "i < x + 1"  
			evaluateExpression(left, LEQ, right + " - 1");
			return;
			
		} else if(op.equals(GT)){
			// Replace "i >= x" by "i > x-1"
			evaluateExpression(left, GEQ, right + " + 1");
			return;
		
		} else if(op.equals(NEQ)){
			// TODO: Make sure this is correct!
			// right is the only undefined number
			low = right + " + 1";
			high = right + " - 1";
			return;
			
		} else if(op.equals(EQ)){
			// right is the only defined number
			low = right;
			high = right;
			return;
		}
		
		throw new Exception("Cannot evaluate quantified expression (" + left + " " + op + " " + right + ")");
	}
	
	/**
	 * Swaps sides of an logical inequality operator
	 * @param op The operator to switch
	 * @return The switched operator
	 */
	private /*@ pure @*/ String changeOrientation(String op){
		switch(op){
		case GEQ: return LEQ;
		case LEQ: return GEQ;
		case GT: return LT;
		case LT: return GT;
		}
		return op;
	}
	
	/**
	 * Returns the code for a range expression limited by two variables
	 */
	public/*@ pure @*/  String translate(){
		return "[" + low + ", " + high + "]";
	}
}