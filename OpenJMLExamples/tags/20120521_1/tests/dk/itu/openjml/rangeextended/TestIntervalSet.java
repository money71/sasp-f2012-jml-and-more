package dk.itu.openjml.rangeextended;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.Iterator;
import dk.itu.openjml.rangeextended.IntervalSet;

import org.junit.Assert;
import org.junit.Test;

public class TestIntervalSet {
	
	@Test
	public void testIntervalSetBasic() {
				
		IntervalSet i = IntervalSet.interval(0, 10);		
		assertNotNull(i);
		
	}

	
	@Test
	public void testIntervalSetBasicForEach() {
				
		IntervalSet i = IntervalSet.interval(0, 10);

		int count = 0;
		for(int n: i){
			assertNotNull(n);
			count++;
		}
		
		assertEquals(11, count);
		
	}
	
	@Test
	public void testIntervalSetBasicIterator() {
				
		IntervalSet i = IntervalSet.interval(0, 10);
		int count = 0;
		Iterator<Integer> ite = i.iterator();

		while(ite.hasNext()){
			assertNotNull(ite.next());
			count++;
		}

		assertEquals(11, count);
		
	}
	
	
}
