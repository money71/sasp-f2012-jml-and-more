package dk.itu.openjml.test;

import static org.junit.Assert.*;
import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

import dk.itu.openjml.range.IntervalSet;

public class Test_IntervalSet {
	
	@Before
	public void setUp() throws Exception {
	}

	@Test
	public void testUnionGap() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 10), IntervalSet.interval(11, 20));
		try{
			String su = "Union: ";
			while(u.hasNext()){
				int n = u.next();
				su += n + "; ";
				assert (0 <= n && n <= 9) || (11 <= n && n <= 19);
			}
			System.out.println(su);
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testIntersection() {
		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 11), IntervalSet.interval(5, 15));
		try{
		String si = "Intersection: ";
		while(i.hasNext()){
			int n = i.next();
			si += n + "; ";
			assert (0 <= n && n <= 10) && (5 <= n && n <= 14);
		}
		System.out.println(si);
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testIntersectedUnion() {
		IntervalSet u = IntervalSet.union(IntervalSet.interval(0, 11), IntervalSet.interval(20, 31));
		IntervalSet iu = IntervalSet.intersect(u, IntervalSet.interval(5, 26));
		try{
		String siu = "Intersected union: ";
		while(iu.hasNext()){
			int n = iu.next();
			siu += n + "; ";
			assert (0 <= n && n <= 10 || 20 <= n && n <= 30) && (5 <= n && n <= 25);
		}
		System.out.println(siu);
		} catch (Exception e){
			Assert.fail();
		}
	}
	
	@Test
	public void testUnitedIntersection() {
		IntervalSet i = IntervalSet.intersect(IntervalSet.interval(0, 101), IntervalSet.interval(50, 151));
		IntervalSet ui = IntervalSet.intersect(i, IntervalSet.interval(5, 26));
		try{
		String sui = "United intersection: ";
		while(ui.hasNext()){
			int n = ui.next();
			sui += n + "; ";
			assert (0 <= n && n <= 100) && (50 <= n && n <= 150) || (5 <= n && n <= 25);
		}
		System.out.println(sui);
		} catch (Exception e){
			Assert.fail();
		}
	}
}
