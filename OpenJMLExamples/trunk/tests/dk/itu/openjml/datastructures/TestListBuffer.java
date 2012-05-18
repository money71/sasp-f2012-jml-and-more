package dk.itu.openjml.datastructures;

import static org.junit.Assert.*;

import org.junit.Test;

import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.ListBuffer;


/**
 * 
 * This test / try out relates to #11
 * Open jml uses a listbuffer in the expressions to represent the declarations
 * e.g. int i, int j ... etc. we have problems doing decl.remove()
 * - decl is a last produced by listbuffer and simply don't support remove()
 *
 */
public class TestListBuffer {

	
	@Test
	public void testJavaCList() {	

		List<String> l1 = List.of("List 1");
		// behind the scene:
		// - hd is set to string
		// - tail is set to an immutable empty list - EMPTY_LIST

		assertEquals("List 1", l1.head);
		assertTrue(l1.tail.isEmpty());

		List<Object> l2 = List.of("List 2", l1);
		assertEquals("List 2", l2.head);
		assertFalse(l2.tail.isEmpty());
	
	}
	


	@Test
	public void testListbufferFirstNext() {
		

		ListBuffer<String> lb = new ListBuffer<String>();
		lb.append("Foo 1");
		lb.append("Foo 2");
		
		assertEquals(2, lb.size());
		
		// first just get no remove
		assertEquals("Foo 1", lb.first());
		assertEquals(2, lb.size());
		
		// next get 1. elm and remove 
		assertEquals("Foo 1", lb.next());
		assertEquals(1, lb.size());
		
	}
	
	@Test
	public void testListbufferPeekPool() {
		
		ListBuffer<String> lb = new ListBuffer<String>();
		lb.append("Foo 1");
		lb.append("Foo 2");
		
		assertEquals(2, lb.size());
		
		// peel just get no remove
		assertEquals("Foo 1", lb.peek());
		assertEquals(2, lb.size());
		
		// poll get 1. elm and remove 
		assertEquals("Foo 1", lb.poll());
		assertEquals(1, lb.size());

	}

	
	@Test
	public void testListbufferWithLists() {
		
		List<String> l1 = List.of("List 1");
		List<String> l2 = List.of("List 2");
		
		ListBuffer<List<String>> lb = new ListBuffer<List<String>>();
		lb.append(l1);
		lb.append(l2);

		assertEquals(2, lb.size());
		
		// first just get no remove
		assertEquals("List 1", lb.first().head);
		assertEquals(2, lb.size());
		
		// next get 1. elm and remove 
		assertEquals("List 1", lb.next().head);
		assertEquals(1, lb.size());
		assertEquals("List 2", lb.first().head);
		
		
		
		
	}
	
	
	
	
}
