package dk.itu.openjml.range;

import java.util.Iterator;

/**
 * A set of intervals over integers. The Interval is a
 * subtype of IntervalSet and can be regarded as a singleton
 * of IntervalSet.
 */
public abstract class IntervalSet implements Iterator{
	
	class NotIncluded extends Exception{
		public NotIncluded(int i){
			super("Number not included in interval: " + i);
		}
	}
	
	IntervalSet left;
	IntervalSet right;
	int current;
	
	/**
	 * Performs union on two IntervalSets
	 * @param l Left IntervalSet
	 * @param r Right IntervalSet
	 * @return An IntervalSet of type UnionIntervalSet
	 */
	public static IntervalSet union(IntervalSet l, IntervalSet r){
		return new UnionIntervalSet(l, r);
	}
	
	/**
	 * Performs intersection on two IntervalSets
	 * @param l Left IntervalSet
	 * @param r Right IntervalSet
	 * @return An IntervalSet of type IntersectionIntervalSet
	 */
	public static IntervalSet intersect(IntervalSet l, IntervalSet r){
		return new IntersectionIntervalSet(l, r);
	}
	
	/**
	 * Only factory that can produce an IntervalSet without two IntervalSets
	 * @param low The lower boundary
	 * @param high The upper boundary
	 * @return An IntervalSet of type Interval describing an interval over integers
	 */
	public static IntervalSet interval(int low, int high){
		return new Interval(low, high);
	}
	
	/**
	 * Internal constructor
	 * @param l Left side of the set
	 * @param r Right side of the set
	 */
	protected IntervalSet(IntervalSet l, IntervalSet r){
		left = l;
		right = r;
		current = Integer.MIN_VALUE;
	}
	
	@Override
	public boolean hasNext() {
		// Check if we reached maximum representable value 
		if(current == Integer.MAX_VALUE){
			return false;
		}
		return isInside(current);
	}

	@Override
	public Object next(){
		return getNext(this.current);
	}

	@Override
	public void remove(){
		// Does nothing
	}
	
	/**
	 * Checks if a given number is inside this IntervalSet (inclusive)
	 * @param current The number to check against
	 * @return True if current is inside, false otherwise
	 */
	abstract protected boolean isInside(int current);
	
	abstract protected int getNext(int current);
}

/**
 * Represents a union of two IntervalSets 
 */
class UnionIntervalSet extends IntervalSet {
	
	protected UnionIntervalSet(IntervalSet l, IntervalSet r){
		super(l, r);
	}
	
	protected boolean isInside(int current){ 
		this.current = current;
		return left.isInside(current) || right.isInside(current);
	}
	
	protected int getNext(int current){
		
		int l = left.getNext(current);
		int r = right.getNext(current);
		
		// Return the number with the lowest absolute distance
		return Math.abs(l - current) < Math.abs (r - current)? l : r;
	}
}

/**
 * Represents an intersection of two IntervalSets 
 */
class IntersectionIntervalSet extends IntervalSet {
	
	protected IntersectionIntervalSet(IntervalSet l, IntervalSet r){
		super(l, r);
	}

	//@ assignable left.current, right.current;
	@Override
	public boolean isInside(int current){
		this.current = current;
		return left.isInside(current) && right.isInside(current);
	}

	@Override
	protected int getNext(int current) {
		int l = left.getNext(current);
		int r = right.getNext(current);
		
		// Return the number with the lowest absolute distance
		return Math.abs(l - current) < Math.abs (r - current)? l : r;
	}
}

/**
 * Represents a singleton of IntervalSet
 */
class Interval extends IntervalSet {
	
	int low;
	int high;
	
	/**
	 * Creates an actual inclusive interval
	 * @param low Lower boundary
	 * @param high Upper boundary
	 */
	protected Interval(int low, int high){
		super(null, null);
		this.low = low;
		this.high = high;
		this.current = this.low;
	}
	
	@Override
	public  boolean hasNext() {
		return isInside(current + 1);
	}
	
	//@ ensures \result == low <= current && current <= high;
	protected /*@ pure @*/ boolean isInside(int current){
		return low <= current && current <= high;
	}

	@Override
	protected int getNext(int current) {
		if(current < low) return low;
		if(current > high) return high;
		this.current = current + 1;
		return this.current;
	}
}