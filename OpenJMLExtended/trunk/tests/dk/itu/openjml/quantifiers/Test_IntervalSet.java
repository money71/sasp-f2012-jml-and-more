package dk.itu.openjml.quantifiers;

import static org.junit.Assert.*;

import java.util.Iterator;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;


/**
 * 
 * Test class for the IntervalSet
 * 
 * Keep the specific min /max values in <b>fresh</b> mind: 
 * Min value: -2147483648
 * Max value: 2147483647
 *
 */
public class Test_IntervalSet {
	
	@Before
	public void setUp() throws Exception {
	}
	
	
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
	
	
	@Test
	public void testUnionGap() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(11, 20), IntervalSet.interval(0, 9));
		try{
			for(int n: u){
				assertTrue("Failed with " + n, 0 <= n && n <= 9 || 11 <= n && n <= 20);
			}
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testIntersection() {
		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 11), IntervalSet.interval(5, 15));
		try{
			for(int n: i){
				assertTrue("Failed with " + n, 0 <= n && n <= 11 && 5 <= n && n <= 15);
			}
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testIntersectedUnion() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(20, 30), IntervalSet.interval(0, 10));
		IntervalSet iu = IntervalSet.intersect(u, IntervalSet.interval(5, 25));
		try{
			for(int n: iu){
				assertTrue("Failed with " + n, 0 <= n && n <= 10 || 20 <= n && n <= 30 && 5 <= n && n <= 25);
			}	
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testUnitedIntersection() {
		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 100), IntervalSet.interval(50, 150));
		IntervalSet ui = IntervalSet.union(i, IntervalSet.interval(40, 60));
		try{				
			for(int n: ui){
				assertTrue("Failed with " + n, 0 <= n && n <= 100 && 50 <= n && n <= 150 || 40 <= n && n <= 60);
			}
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testNotInside() {
		IntervalSet ni = IntervalSet.union(IntervalSet.interval(0, 100), IntervalSet.interval(51, 49));
		try{				
			for(int n: ni){
				assertTrue("Failed with " + n, 0 <= n && n <= 100 && n != 50);
			}
		} catch (Exception e){
			Assert.fail();
		}
	}	
	
	/**
	 * (2147483645, 2147483647] => 
	 * (2147483645, 2147483646)
	 */	
	@Test
	public void testUnionMaxValue() {
		IntervalSet u = IntervalSet.interval(Integer.MAX_VALUE-2, Integer.MAX_VALUE);
		try{
			int count = 0;
			for(int n: u){
				assertTrue("Failed with " + n, Integer.MAX_VALUE-2 <= n && n <= Integer.MAX_VALUE);
				count++;
			}
			assertEquals(3, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}

	/** 
	 * (-2147483648, -2147483646] => 
	 * (-2147483648, -2147483647)
	 */	
	@Test
	public void testUnionMinValue() {
		IntervalSet u = IntervalSet.interval(Integer.MIN_VALUE, Integer.MIN_VALUE+2);
		try{
			int count = 0;
			for(int n: u){
				assertTrue("Failed with " + n, Integer.MIN_VALUE <= n && n <= Integer.MIN_VALUE+2);
				count++;
			}
			assertEquals(3, count);			
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testSingleValue() {
		IntervalSet i = IntervalSet.interval(0, 0);
		try{
			int count = 0;
			for(int n: i){
				assertTrue(n == 0);
				count++;
			}
			assertEquals(1, count);	
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	
	// NOTE: #26 
	@Test
	public void testUnionSingleton() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 0), IntervalSet.interval(10, 10));
		try{
			int count = 0;
			for(int n: u){
				assertTrue(n == 0 || n == 10);
				count++;
			}
			assertEquals(2, count);	
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testOverlappingIntersection() {
		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 20), IntervalSet.interval(0, 10));
		try{
			for(int n: i){
				assertTrue("Failed with " + n, 0 <= n && n <= 20 && n <= 10);
			}
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testOverlappingUnion() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 20), IntervalSet.interval(0, 10));
		try{
			for(int n: u){
				assertTrue("Failed with " + n, 0 <= n && (n <= 20 || n <= 10));
			}
		} catch (Exception e){
			Assert.fail();
		}
	}
}