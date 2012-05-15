package dk.itu.openjml.quantifiers;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import com.sun.tools.javac.tree.JCTree.JCExpression;

/**
 * This class represents a quantified range over integers.
 * It walks over an expression tree and translate atomic
 * boolean expressions into a set of values. As an atomic
 * boolean expression can only define one margin of a range,
 * the other margin will by default be Integer.MAX_VALUE or
 * respectively Integer.MIN_VALUE. Through operations on
 * sets these loose margins will be reduced to a valid
 * set of ranges. It should be able 
 *
 */
public abstract class QRange {
	
	// Conjunction and disjunction
	final static String CON = "&&";
	final static String DIS = "||";
	
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
		if(e instanceof JmlBinary){
			if(isConjunction((JmlBinary)e)) { // Conjunction
				return new IntersectionQRange((JmlBinary)e, var);
				
			} else if(isDisjunction((JmlBinary)e)) { // Disjunction
				return new UnionQRange((JmlBinary)e, var);
				
			} else if(isAtomic((JmlBinary)e)){ // Leaf node holding value
				return new LeafQRange((JmlBinary)e, var);
			} 
			// TODO: Add pure method calls?
		}
		throw new Exception("Cannot execute this statement."); // FIXME: Do this properly
	}
	
	public QRange(JmlBinary e, String var) throws Exception{
		left = compute(e.lhs, var);
		right = compute(e.rhs, var);
	}
	
	// Empty default
	protected QRange(){
		left = null;
		right = null;
	}
	
	/**
	 * Checks if an expression contains a variable name
	 * @param e The expression tree
	 * @param var The variable name
	 * @return True if e contains var, false otherwise
	 */
	static boolean containsVar(JCExpression e, String var){
		if(e instanceof JmlBinary){
			return containsVar(((JmlBinary)e).lhs, var) || containsVar(((JmlBinary)e).rhs, var);
		}
		// FIXME: Do this the proper way
		return e.toString().contains(var);
	}
	
	static // Checks the expression tree for an "&&" operator
	boolean isConjunction(JmlBinary e){
		return e.op.toString() == CON;
	}
	
	// Checks the expression tree for an "||" operator
	static boolean isDisjunction(JmlBinary e){
		return e.op.toString() == DIS;
	}
	
	// Check if the expression is atomic (left and right side hold values
	static boolean isAtomic(JmlBinary e){
		return e.op.toString() == GT ||
				e.op.toString() == EQ ||
				e.op.toString() == LT ||
				e.op.toString() == GEQ ||
				e.op.toString() == LEQ;
	}
	
	abstract public String translate();
}

class UnionQRange extends QRange {
	
	public UnionQRange(JmlBinary e, String var) throws Exception{
		super(e, var);
	}
	
	public String translate(){
		return "";
	}
	
}

class IntersectionQRange extends QRange {
	
	public IntersectionQRange(JmlBinary e, String var) throws Exception{
		super(e, var);
	}
	
	public String translate(){
		return "";
	}
}

class LeafQRange extends QRange {
	
	String var;
	String low;
	String high;
	int ilow;
	int ihigh;
	
	public LeafQRange(JmlBinary e, String var) throws Exception{
		// Store the variable name
		this.var = var;
		
		ilow = Integer.MIN_VALUE;
		ihigh = Integer.MAX_VALUE;
		
		String left = e.lhs.toString();
		String op = e.op.toString();
		String right = e.rhs.toString();
		
		evaluateExpression(left, op, right);
		
	}
	
	// TODO: Write specs!
	/**
	 * Evaluates an expression made from three strings, left,
	 * op, right, after these rules:
	 * 
	 * e[l o r] =: 
	 *   r = var && !(l = var) ==> e[l o^(-1) r]
	 * | o = "<=" ==> e[l "<" (r + 1)]
	 * | o = ">=" ==> e[l ">" (r - 1)]
	 * | o = "<" ==> high = r
	 * | o = ">" ==> low = r
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
		
		} else if(op == LEQ){
			// Replace "i <= x" by "i < x + 1"  
			evaluateExpression(left, LT, right + " + 1");
			
		} else if(op == GEQ){
			// Replace "i >= x" by "i > x-1"
			evaluateExpression(left, GT, right + " - 1");
		
		} else if(op == LT){
			// Right is the maximum value
			high = right;
			
		} else if(op == GT){
			// Right is the minimum value
			low = right;
		
		} else if(op == NEQ){
			// TODO: Make sure this is correct!
			// right is the only undefined number
			low = right + " + 1";
			high = right + " - 1";
			
		} else if(op == EQ){
			// right is the only defined number
			low = right;
			high = right;
		}
		
		throw new Exception("Cannot evaluate quantified expression (" + left + " " + op + " " + right + ")");
	}
	
	/**
	 * Inverts a logical operator for when it's 
	 * @param op
	 * @return
	 */
	private String changeOrientation(String op){
		switch(op){
		case GEQ: return LEQ;
		case LEQ: return GEQ;
		case GT: return LT;
		case LT: return GT;
		}
		return op;
	}
	
	public String translate(){
		return "";
	}
}

