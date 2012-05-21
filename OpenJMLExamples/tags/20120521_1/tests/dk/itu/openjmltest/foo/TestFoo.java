package dk.itu.openjmltest.foo;

import org.junit.Assert;
import org.junit.Test;

import dk.itu.openjml.foo.Foo;

public class TestFoo {
	
	@Test
	public void testFoo() 
	{
		
		Foo foo = new Foo();
		
		Assert.assertNotNull(foo);

	}	
	
}
