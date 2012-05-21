package dk.itu.openjml.test;

import org.junit.runner.RunWith;  
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses( {  
	Test_ForAll.class,
	Test_ForAllNaive.class,
	Test_IntervalSet.class,
	Test_QRange.class
} )
public class TestAll {

}

