package dk.itu.openjml.interval;

/**
 * Data type for intervals on the real line with integer endpoints.
 *  
 * Based upon:
 * http://introcs.cs.princeton.edu/java/32class/
 * http://introcs.cs.princeton.edu/java/32class/Interval.java.html
 * 
 * TODO: clean up the jml specs
 * 
 */
public class IntervalSimple {

    private /*@ public_ @*/ int left;
    private /*@ public_ @*/ int right;
    
    //@ assignable left, right;
    //@ requires left =< right;
    public IntervalSimple(int left, int right) {
        //assert (left <= right);
    	// 
        this.left  = left;
        this.right = right;
    }

    public /*@ pure @*/ int getLeft()  { return left;  }
    public /*@ pure @*/ int getRight() { return right; }

    // does this interval a intersect b?
    public /*@ pure @*/ boolean intersects(IntervalSimple b) {
        IntervalSimple a = this;
        if (b.left <= a.right && b.left >= a.left) { return true; }
        if (a.left <= b.right && a.left >= b.left) { return true; }
        return false;
    }

    public String toString() {
        return "[" + left + ", " + right + "]";
    }	
	
}
