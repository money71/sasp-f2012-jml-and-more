package dk.itu.openjml.rangeextended;

import java.util.Iterator;


//import dk.itu.openjml.range.Interval;
//import dk.itu.openjml.range.IntervalSet;



/**
 * A set of intervals over integers. The Interval is a
 * subtype of IntervalSet and can be regarded as a singleton
 * of IntervalSet.
 * 
 * FIXME: Interval is *left-inclusive* and *right-exclusive*, so we cannot process Integer.MAX_VALUE #19
 * 
 * Note: its a spin off from src/dk/itu/openjml/range/IntervalSet.java < r160
 * and start for a solution on #18 but it turned out not to be simple to set up an
 * IntervalSetIterator at least not in the context of the time we have left...
 * 
 * this version might have moved to many methods from the IntervalSet 
 * to the IntervalSetIterator - it will require some fresh eye's and probably not 
 * result in an easy to read class's - the effort should then also take in
 * consideration to use an more generic approach then *only* Integer #22
 * 
 */
public abstract class IntervalSet implements Iterable<Integer>{

	protected /*@ nullable @*/ IntervalSet left;
	protected /*@ nullable @*/ IntervalSet right;	
	protected boolean initialized;
	protected int low;
	protected int high;
	protected int current;
	
	/**
	 * Internal constructor
	 * @param l Left side of the set
	 * @param r Right side of the set
	 */
	protected IntervalSet(/*@ nullable @*/ IntervalSet l, /*@ nullable @*/ IntervalSet r){
		left = l;
		right = r;
		current = Integer.MIN_VALUE;
		initialized = false;
	}

	// TODO: possible insert factories for union and intersection
	
	
	/**
	 * Only factory that can produce an IntervalSet without two IntervalSets
	 * - both values are inclusive in the interval.
	 * 
	 * @param low The lower boundary
	 * @param high The upper boundary
	 * @return An IntervalSet of type Interval describing an interval over integers
	 */
	//@ ensures \fresh(\result)
	public static IntervalSet interval(int low, int high){
	//public static IntervalSet interval(int low, int high){
	// module approach didn't like static
		return new Interval(low, high);

	}

	
}




/**
 * Represents a singleton of IntervalSet
 * It is left-inclusive and right-exclusive!
 */
class Interval extends IntervalSet {
		
	/**
	 * Creates an actual left-inclusive right-exclusive interval
	 * @param low Lower boundary
	 * @param high Upper boundary
	 */
	//@ assignable left, right, low, high, current;
	protected Interval(int low, int high){
		super(null, null);
		this.low = low;
		this.high = high;
		this.current = this.low;
	}
	
	@Override
	public Iterator<Integer> iterator() {
		return new IntervalIterator(low, high, current);
		
	}
	
	
}


//public class IntervalSetIterator<T extends Comparable<T>> implements Iterator<T>{
abstract class IntervalSetIterator implements Iterator<Integer>{
	
	protected int low;
	protected int high;
	protected int current;
	protected boolean initialized; 
	
	//constructor
	public IntervalSetIterator(int low, int high, int current) {
		this.current = current;
		this.low = low;
		this.high = high;
//		this.initialized = initialized; 
	}
	
	
	//@ requires !initialized || current == high;
	//@ assignable low, high, current;
	//@ also
	//@ requires low <= current;
	//@ requires current < high;
	//@ ensures \result == true;
	//@ also
	//@ requires low > current || current >= high;
	//@ ensures \result == false;
	public boolean hasNext() {
		// Get the next valid range
		if(!initialized || current == high){
			initialized = true;
			getNextRange();
		}
		return low <= current && current < high;
	}

	//@ ensures \result == current - 1;
	//@ ensures_redundantly \result == \old(current);
	public Integer next(){
		// Check sets up all the ranges, just in case
		if(hasNext()){
			int r = current;
			current++;
			return r;
		}
		return current;
	}
	
	/**
	 * This is implemented because Iterator requires it.
	 */
	public void remove(){
        throw new UnsupportedOperationException();
	}
	
	/**
	 * Find the next valid range for this IntervalSet
	 */
	//@ ensures current == low;
	//@ assignable low, high, current;
	//@ ensures \old(current) <= current;
	protected void getNextRange(){
		low = getNextLow(current);
		high = getNextHigh(current);
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
	abstract protected /*@ pure @*/ int getNextLow(int current);
	
	/**
	 * Returns the next valid high for current 
	 * @param current
	 * @return
	 */
	abstract protected /*@ pure @*/ int getNextHigh(int current);
	
	
	
}


class IntervalIterator extends IntervalSetIterator {
	
	
	public IntervalIterator(int low, int high, int current) {
		super(low, high, current);
	}

	//@ ensures low <= current && current <= high;
	@Override
	protected /*@ pure @*/ boolean isInside(int current){
		return super.low <= current && current <= super.high;
	}
	
	//@ ensures \result == isInside(current);
	@Override
	public /*@ pure @*/ boolean hasNext(){
		return isInside(super.current);
	}
	

	//@ ensures \result == this.low;
	@Override
	protected int getNextLow(int current) {
		return super.low;
	}

	//@ ensures \result == this.high;
	@Override
	protected int getNextHigh(int current) {
		return super.high;
	}
	
}











