package dk.itu.openjml.quantifiers;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlExpression;

public class QIntegrals {
	
}

/**
 * Runs at compile-time. 
 * Represents a set of valid numbers trying not using polyhedral analysis.
 */
abstract class QRange {
	QRange left;
	QRange right;
	
	public QRange(JmlExpression e, String var){
		if (e instanceof JmlBinary){
			QRange left = new QRange(((JmlBinary) e).lhs, var);
			if (((JmlBinary) e).op.toString() == QRangeUnion.OPERATOR){
				
			} else if (((JmlBinary) e).op.toString() == QRangeIntersection.OPERATOR){
				
			} else { 
				/* Translate this token after the following rules:
				 * (i is the variable of concern)
				 * 
				 * i >= j || j <= i --> i > (j-1)
				 * i > j  || j < i 	--> i > j
				 * i <= j || j >= i	--> i < (j+1)
				 * i < j  || j > i	--> i < j
				 * i == j || j == i	--> i == j
				 * i != j || j != i	--> i != j
				 * 
				 * FIXME: But what about implications?
				 */
				
			}
		}
	}
	
	public QRange(QRange left, QRange right){
		this.left = left;
		this.right = right;
	}
	
	public static QRange generateRange(JmlExpression e, String var){
		
		QRange range;
		
		if (e instanceof JmlBinary){ // JmlExpression is binary
			
		}
		
		return range;
	}
	
	public int getLow(){
		int left = this.left.getLow();
		int right = this.right.getLow();
		return left < right? left : right;
	}
	
	public int getHigh(){
		int left = this.left.getHigh();
		int right = this.right.getHigh();
		return left < right? left : right;
	}
	
	abstract public /*@ pure @*/ String translate();
}

/**
 * Represents a union of two 
 *
 */
class QRangeUnion extends QRange{
	final static String OPERATOR = "||";
	
	public QRangeUnion(QRange left, QRange right){
		super(left, right);
	}
	
	public String translate(){
		return "";
	}
}

class QRangeIntersection extends QRange{
	final static String OPERATOR = "&&";
	
	public QRangeIntersection(QRange left, QRange right){
		super(left, right);
	}
	
	public String translate(){
		return "";
	}
}

class QRangeLeaf extends QRange {
	private int low;
	private int high;
	
	public QRangeLeaf(int low, int high){
		super(null, null);
		this.low = low;
		this.high = high;
	}
	
	public int getLow(){
		return low;
	}
	
	public int getHigh(){
		return high;
	}
	
	public String translate(){
		return "";
	}
}