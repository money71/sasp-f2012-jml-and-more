package dk.itu.openjml.interval;

import static org.junit.Assert.*;

import org.junit.Test;

/**
 * 
 * General approach keep less side effects as possible
 * - might result in *final* abuse - think that over later. 
 *
 */
public class TestIntervalTryout1 {

	
	static class Range {
		
		private final int low;
		private final int hi;
		
		// TODO:  probably set up an invariant for low/hi no null
		// and low =< hi
		
	    public Range(int low, int hi) {
	        this.low  = low;
	        this.hi = hi;
	    }
	    
	    // TODO: not sure if pure can be used together with final
	    public /*@ pure @*/ final int getLow() { return this.low; }
	    
	    public /*@ pure @*/ final int getHi() { return this.hi; }
		
	    public final String toString() {
	        return "Range(" + getLow() + "," + getHi() + ")";
	    }
	    
	}

	static class Disjunction {

		private final Range a;
		private final Range b;		
		
	    public Disjunction(Range a, Range b) {
	    	
	    	// does the ranges overlap ? 
	    	// if so merge
	    	// else return ranges
	    	
	    	if(intersects(a, b)) {
	    		this.a = merge(a,b);
	    		this.b = null; // not niece i guess - we could use an option/none type
	    	} else {
	    		// do we need to order this to full fill getLowBound / getHighBound
	    		// if so do it otherwise probably rename the methods.
		        this.a  = a;
		        this.b = b;	    		
	    	}
	    }
	    
	    public /*@ pure @*/ final Range getLowBound() { return this.a; }
	    
	    public /*@ pure @*/ final Range getHighBound() { return this.b; }
	    
	}
	
	
	// addhoc functions cleanup later
    // does this interval a intersect b?
    public static /*@ pure @*/ boolean intersects(Range a, Range b) {
        if (b.getLow() <= a.getHi() && b.getLow() >= a.getLow()) { return true; }
        if (a.getLow() <= b.getHi() && a.getLow() >= b.getLow()) { return true; }
        return false;
    }

    //@ requires a,b not be null
    // is its /*@ pure @*/ its at least \fresh(\result) - right ?
    public static Range merge(Range a, Range b) {
    	final int lo = a.getLow() <= b.getLow() ? a.getLow() : b.getLow();
    	final int hi = a.getHi()  >= b.getHi()  ? a.getHi()  : b.getHi();;    	    	
    	return new Range(lo, hi);
    }
    
	
	@Test
	public void testRanges() {
		Range r1 = new Range(15, 20);
		assertEquals(20, r1.getHi());
		assertEquals(15, r1.getLow());
	}

	@Test
	public void testRangesIntersect() {
		Range r1 = new Range(15, 20);
		Range r2 = new Range(18, 22);
		assertTrue(intersects(r1, r2));
		assertTrue(intersects(r2, r1));
		
		Range r3 = new Range(-15, 20);
		Range r4 = new Range(200, 400);
		assertFalse(intersects(r3, r4));
		assertFalse(intersects(r4, r3));
		
	}

	@Test
	public void testRangesMerge() {
		Range r1 = new Range(15, 20);
		Range r2 = new Range(18, 22);

		Range r1r2 = merge(r1, r2);
		
		assertEquals(15, r1r2.getLow());
		assertEquals(22, r1r2.getHi());

		Range r2r1 = merge(r2, r1);
		assertEquals(15, r2r1.getLow());
		assertEquals(22, r2r1.getHi());
		
	}
	
	
	@Test
	public void testDisjunctionRanges() {
		Disjunction d = new Disjunction( new Range(15, 20), new Range(25, 35) );

		assertEquals(15, d.getLowBound().getLow());
		assertEquals(20, d.getLowBound().getHi());
		assertEquals(25, d.getHighBound().getLow());
		assertEquals(35, d.getHighBound().getHi());

//		System.out.println(d.getLowBound());
//		System.out.println(d.getHighBound());
		
		Disjunction d2 = new Disjunction( new Range(15, 30), new Range(25, 35) );

		assertEquals(15, d2.getLowBound().getLow());
		assertEquals(35, d2.getLowBound().getHi());		

		// assertNull(d2.getLowBound());		
		
//		System.out.println(d2.getLowBound());
//		System.out.println(d2.getHighBound());

	}

	
	
	
	
}
