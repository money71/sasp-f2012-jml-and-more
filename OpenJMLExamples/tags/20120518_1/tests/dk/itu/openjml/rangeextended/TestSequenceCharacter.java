package dk.itu.openjml.rangeextended;

import dk.itu.openjml.rangeextended.SequenceCharacter; 

import org.junit.Assert;
import org.junit.Test;

public class TestSequenceCharacter {
	
	@Test
	public void testSequenceCharacterBasic()
	{
		
		SequenceCharacter s = new SequenceCharacter('b');
		
		Assert.assertEquals(new Character('c'), s.next().value());
		Assert.assertEquals(new Character('a'), s.previous().value());
		
	}	
	
}
