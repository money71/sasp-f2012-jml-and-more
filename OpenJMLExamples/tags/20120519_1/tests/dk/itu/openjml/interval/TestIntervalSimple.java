package dk.itu.openjml.interval;

import org.junit.Assert;
import org.junit.Test;

public class TestIntervalSimple {

	@Test
	public void testIntervalSimpleIntersects() {

		IntervalSimple a = new IntervalSimple(15, 20);
        
        IntervalSimple b = new IntervalSimple(25, 30);
                
        IntervalSimple c = new IntervalSimple(10, 40);

        IntervalSimple d = new IntervalSimple(40, 50);
                
        Assert.assertFalse(b.intersects(a));
        Assert.assertFalse(a.intersects(b));
        Assert.assertTrue(a.intersects(c));
        Assert.assertFalse(a.intersects(d));
        Assert.assertTrue(b.intersects(c));
        Assert.assertFalse(b.intersects(d));
        Assert.assertTrue(c.intersects(d));
        
	}
	
}
