package dk.itu.openjml.rangeextended;

import org.junit.runner.RunWith; 
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses( {  
	TestSequenceInteger.class,
	TestSequenceCharacter.class,
	TestRange.class,
	TestCollection.class,
	TestIntervalSet.class
} )
public class TestAll {

}

