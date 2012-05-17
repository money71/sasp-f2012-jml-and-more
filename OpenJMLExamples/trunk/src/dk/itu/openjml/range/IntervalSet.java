package dk.itu.openjml.range;

import java.util.Iterator;

/**
 * A set of intervals over integers. The Interval is a
 * subtype of IntervalSet and can be regarded as a singleton
 * of IntervalSet.
 * 
 * @note Interval is *left-inclusive* and *right-exclusive*!
 */
public abstract class IntervalSet implements Iterator<Integer>{
	
	IntervalSet left;
	IntervalSet right;
	
	private boolean initialized;
	
	int low;
	int high;
	protected int current;
	
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
		initialized = false;
	}
	
	@Override
	public boolean hasNext() {
		// Get the next valid range
		if(!initialized || current == high){
			initialized = true;
			getNextRange();
		}
		return low <= current && current < high;
	}

	@Override
	public Integer next(){
		// Check sets up all the ranges, just in case
		if(hasNext()){
			int r = current;
			current++;
			return r;
		}
		return current;
	}

	@Override
	public void remove(){
		// Does nothing
	}
	
	/**
	 * Find the next valid range for this IntervalSet
	 */
	protected void getNextRange(){
		low = getNextLow(current);
		high = getNextHigh(current);// + 1; // FIXME: This is a hack to get inclusive high boundary
		
		// Set current to the new low
		current = low;
	}
	
	/**
	 * Checks if a given number is inside this IntervalSet (inclusive)
	 * @param current The number to check against
	 * @return True if current is inside, false otherwise
	 */
	abstract protected boolean isInside(int current);
	
	/**
	 * Returns the next valid low after current
	 * @param current The current number active.
	 * @return The new low. If there is no valid new low, return current again.
	 */
	abstract protected int getNextLow(int current);
	
	/**
	 * Returns the next valid high for current 
	 * @param current
	 * @return
	 */
	abstract protected int getNextHigh(int current);
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
	
	/**
	 * Union can answer two different lows!
	 */
	protected int getNextLow(int current){
		int l = left.getNextLow(current);
		int r = right.getNextLow(current);
		
		// If both are higher than current
		if(current < l && current < r){
			// Return the smaller low
			return l < r ? l : r;
		
		// Else return the one that is higher than current
		} else if(current < l){
			return l;
		} else if(current < r){
			return r;
		}
		
		// If none of this holds, return current again
		return current;
	}

	protected int getNextHigh(int current) {
		int l = left.getNextHigh(current);
		int r = right.getNextHigh(current);
		
		// If both are higher than current
		if(current < l && current < r){
			// Return the smaller high
			return l < r ? l : r;
		
		// Else return the one that is higher than current
		} else if(current < l){
			return l;
		} else if(current < r){
			return r;
		}
		
		// If none of this holds, return current again
		return current;
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
	public boolean isInside(int current){
		this.current = current;
		return left.isInside(current) && right.isInside(current);
	}

	protected int getNextLow(int current) {
		int l = left.getNextLow(current);
		int r = right.getNextLow(current);
		
		// When current is lower than any of these, return
		// the higher low.
		if(current < l || current < r){
			return l < r ? r : l;
		}
		
		// Else just return current
		return current;
	}

	protected int getNextHigh(int current) {
		int l = left.getNextHigh(current);
		int r = right.getNextHigh(current);
		
		// When current is lower than any of these, return
		// the lower high.
		if(current < l || current < r){
			return l < r ? l : r;
		}
		
		// Else just return current
		return current;
	}
}

/**
 * Represents a singleton of IntervalSet
 * It is left-inclusive and right-exclusive!
 */
class Interval extends IntervalSet {
		
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
	
	public boolean hasNext() {
		return isInside(current);
	}
	
	//@ ensures \result == low <= current && current <= high;
	protected /*@ pure @*/ boolean isInside(int current){
		return low <= current && current <= high;
	}
	
	//@ ensures \result == this.low
	protected int getNextLow(int current) {
		return low;
	}
	
	//@ ensures \result == this.high
	protected int getNextHigh(int current) {
		return high;
	}
}