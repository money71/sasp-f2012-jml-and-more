package dk.itu.openjml.quantifiers;

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
	
	/**
	 * Thrown if a quantified expression can not be evaluated properly so
	 * that it can be executed in RAC. 
	 */
	public static class NotExecutableQuantifiedExpr extends Exception {
		private static final long serialVersionUID = 1L;

		public NotExecutableQuantifiedExpr(String expr){
			super("Cannot evaluate quantified expression [" + expr + "]");
		}
	}
	
	// Conjunction and disjunction
	final static String CON = "&&";
	final static String DIS = "||";
	
	// Implications (NOTE: Currently not supported #12)
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
	protected /*@ spec_public @*/ QRange left;
	protected /*@ spec_public @*/ QRange right;
	
	/**
	 * Returns an instance of QRange that represents a (set of) range(s)
	 * @param e An expression defining the range
	 * @param var A variable for which the range should be computed for
	 * @return A new QRange for the given expression and variable
	 * @throws NotExecutableQuantifiedExpr Thrown if the expression contains logical operations we are not willing or able to process.
	 */
	public static QRange compute(JCExpression e, String var) throws NotExecutableQuantifiedExpr{
		
		// Ignore the expression if var is not defined anywhere in this expression
		if(!definesVar(e, var)){
			return new IgnoreQRange();
		}
		
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
			// NOTE: #13
		}
		throw new NotExecutableQuantifiedExpr(e.toString());
	}
	
	/**
	 * Build a QRange object that holds QRanges through compute
	 * @param e A JmlBinay expression which describes a range
	 * @param var A variable name for which we want to find the range
	 * @throws NotExecutableQuantifiedExpr If e is not an executable statement
	 */
	//@ assignable left, right;
	//@ ensures \fresh(left);
	//@ ensures \fresh(right);
	public QRange(JCBinary e, String var) throws NotExecutableQuantifiedExpr{
		left = compute(e.lhs, var);
		right = compute(e.rhs, var);
	}
	
	/**
	 * Empty default constructor
	 */
	//@ ensures left == null;
	//@ ensures right == null;
	protected QRange(){
		left = null;
		right = null;
	}
	
	/**
	 * Checks recursively if an expression defines a variable name,
	 * i.e. if any subexpression consists of only the variable.
	 * @param e The expression tree
	 * @param var The variable name
	 * @return True if e or any subexpression of e defines var, false otherwise
	 */
	static /*@ pure @*/ boolean definesVar(JCExpression e, String var){
		if(e instanceof JCBinary){
			return definesVar(((JCBinary)e).lhs, var) || definesVar(((JCBinary)e).rhs, var);
		}
		// FIXME: Do this the proper way at one point #14
		return e.toString().equals(var);
	}
	
	/**
	 * Checks a JmlBinary expression for a given operator
	 * @param e A JmlBinary expression
	 * @param o Some operator
	 * @return True if o is the operator in e
	 */
	public static /*@ pure @*/ boolean hasOperator(JCBinary e, String o){
		return getOperator(e).equals(o);
	}
	
	/**
	 * Returns a string which is the operator of a JCBinary expression
	 * @param e A JCBinary expression
	 * @return The operator in e
	 */
	//@ ensures fresh(\result);
	public static String getOperator(JCBinary e){
		// NOTE: Could probably be improved #15
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
	public static /*@ pure @*/ boolean isAtomic(JCBinary e){
		return hasOperator(e, GT) ||
				hasOperator(e, EQ) ||
				hasOperator(e, LT) ||
				hasOperator(e, GEQ) ||
				hasOperator(e, LEQ);
	}
	
	/**
	 * Generates source code for this range.
	 * Returns no operator if one of the child ranges is empty
	 * and instead just returns the opposite child's code.
	 * 
	 * @return Source code to build the range defined by this QRange
	 */
	//@ requires left != null;
	//@ requires right != null;
	
	public /*@ pure @*/ String translate(){
		if(left.ignore()){
			return right.translate();
		} else if(right.ignore()){
			return left.translate();
		}
		return getCode();
	}
	
	public /*@ pure @*/ String toString(){
		return translate();
	}
	
	/**
	 * @return The actual operation for this range to be performed in source code
	 */
	abstract protected /*@ pure @*/ String getCode();
	
	/**
	 * @return True if the fields left and right are null
	 */
	public /*@ pure @*/ boolean isLeaf(){
		return left == null && right == null;
	}
	
	/**
	 * @return True if this is empty, false otherwise
	 */
	public /*@ pure @*/ boolean ignore(){
		return this instanceof IgnoreQRange;
	}
}

/**
 * Represents a union of two ranges
 */
class UnionQRange extends QRange {
	
	public UnionQRange(JCBinary e, String var) throws NotExecutableQuantifiedExpr{
		super(e, var);
	}
	
	/**
	 * @returns The code for a union-operation on ranges
	 */
	public /*@ pure @*/ String getCode(){
		return "dk.itu.openjml.quantifiers.Intervalset.union(" + left.translate() + ", " + right.translate() + ")";
	}
}

/**
 * Represents an intersection of two ranges 
 */
class IntersectionQRange extends QRange {
	
	public IntersectionQRange(JCBinary e, String var) throws NotExecutableQuantifiedExpr{
		super(e, var);
	}
	
	/**
	 * Get code
	 * - here its a real code call, imagine on the rac.
	 * @returns The code for an intersection-operation on ranges
	 */
	protected /*@ pure @*/ String getCode(){
		// FIXME: #23 set right package path when project is moved to final.
		return "dk.itu.openjml.quantifiers.IntervalSet.intersect(" + left.translate() + ", " + right.translate() + ")";
	}
}

/**
 * Represents a range defined through a boolean expression
 */
class LeafQRange extends QRange {
	
	String var;
	String low;
	String high;
	
	public LeafQRange(){
		low = "Integer.MIN_VALUE";
		high = "Integer.MAX_VALUE";
		left = null;
		right = null;
	}
	
	public LeafQRange(JCBinary e, String var) throws NotExecutableQuantifiedExpr{
		// Store the variable name
		this.var = var;
		
		low = "Integer.MIN_VALUE";
		high = "Integer.MAX_VALUE";
		
		String left = e.lhs.toString();
		String op = getOperator(e);
		String right = e.rhs.toString();
		
		evaluateExpression(left, op, right);
	}
	
	// TODO: Write specs! #16
	/**
	 * Evaluates an expression made from three strings, left,
	 * op, right, after these rules:
	 * 
	 * (Note: had to switch rules 1 and 3 and 2 and 4 to guarantee inclusive ranges.)
	 * 
	 * e[l o r] =: 
	 *   r = var && !(var not in l) ==> e[l o^(-1) r]
	 * | o = "<=" ==> high = r
	 * | o = ">=" ==> low = r
	 * | o = "<" ==> e[l "<=" (r - 1)]
	 * | o = ">" ==> e[l ">=" (r + 1)]
	 * | o = "!=" ==> low = (r + 1) && high = (r - 1)
	 * | o = "==" ==> low = r && high = r
	 * | _ ==> not defined
	 * 
	 * @param left A value or a identifier
	 * @param op A operator
	 * @param right A value or an identifier
	 * @throws NotExecutableQuantifiedExpr if none of the rules apply to this expression
	 */
	//@ assignable low, high;
	private void evaluateExpression(String left, String op, String right) throws NotExecutableQuantifiedExpr{
		
		if(right.equals(var) && !left.contains(var)){
			evaluateExpression(right, changeOrientation(op), left);
		
		} else if(op.equals(LEQ)){
			high = right;
			
		} else if(op.equals(GEQ)){
			low = right;
		
		} else if(op.equals(LT)){
			evaluateExpression(left, LEQ, right + " - 1");
			
		} else if(op.equals(GT)){
			evaluateExpression(left, GEQ, right + " + 1");
		
		} else if(op.equals(NEQ)){
			// This is correct for inclusive intervals!
			low = right + " + 1";
			high = right + " - 1";
			
		} else if(op.equals(EQ)){
			// right is the only defined number
			low = right;
			high = right;

		} else {
			throw new NotExecutableQuantifiedExpr(left + " " + op + " " + right);
		}
	}
	
	/**
	 * Swaps orientation of a logical inequality operator
	 * @param op The operator to switch
	 * @return The switched operator
	 */
	private /*@ pure @*/ String changeOrientation(String op){
		switch(op){
		case GEQ: return LEQ;
		case LEQ: return GEQ;
		case GT:  return LT;
		case LT:  return GT;
		// other examples do the return here as:
		// default:  return op;
		// but then jml 2 check complains: Method "changeOrientation" must return a value
		}
		return op;
	}
	
	/**
	 * @returns The code for a range expression limited by two variables
	 */
	public /*@ pure @*/  String translate(){
		// FIXME: #23 set right package path when project is moved to final.
		return "dk.itu.openjml.quantifiers.IntervalSet.interval(" + low + ", " + high + ")";
	}
	
	/**
	 * @returns Empty string
	 */
	protected /*@ pure @*/ String getCode(){
		return "";
	}
}

class IgnoreQRange extends LeafQRange {
	
	/**
	 * Creates a leaf that has no meaning for an expression
	 */
	public IgnoreQRange(){
		super();
		low = null;
		high = null;
	}
	
	public /*@ pure @*/ String translate(){
		return "null";
	}
}