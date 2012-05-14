package dk.itu.openjml.quantifiers;

import java.util.Set;

import org.jmlspecs.openjml.JmlTree.JmlBinary;
import org.jmlspecs.openjml.JmlTree.JmlExpression;

abstract class QSet {	
	QSet l;
	QSet r;
	
	public QSet(QSet l, QSet r){
		this.l = l;
		this.r = r;
	}
	
	public static QSet generateRange(JmlExpression e, String v){
		
	}
	
	public QSet union(QSet l, QSet r){
		return new QUnion(l, r);
	}
	
	public QSet intersect(QSet l, QSet r){
		return new QIntersection(l, r);
	}
	
	public abstract /*@ pure @*/ String toSource();
}

/**
 * Represents a union of two sets 
 */
class QUnion extends QSet {
	final String OPERATOR = "||";
	
	public QUnion(QSet l, QSet r){super(l, r);} 
	
	@Override
	public String toSource() {
		// TODO Auto-generated method stub
		return null;
	}
}

/**
 * Represents an intersection of two sets 
 */
class QIntersection extends QSet {
	final String OPERATOR = "&&";
	
	public QIntersection(QSet l, QSet r){super(l, r);} 
	
	@Override
	public String toSource() {
		// TODO Auto-generated method stub
		return null;
	}
}