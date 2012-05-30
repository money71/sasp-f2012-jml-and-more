// $ANTLR 3.4 /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g 2012-05-30 22:11:28

  package dk.itu.htmldoc;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked"})
public class HtmlDocLexer extends Lexer {
    public static final int EOF=-1;
    public static final int T__8=8;
    public static final int T__9=9;
    public static final int T__10=10;
    public static final int T__11=11;
    public static final int T__12=12;
    public static final int T__13=13;
    public static final int BODY=4;
    public static final int DOC=5;
    public static final int TEXT=6;
    public static final int TITLE=7;

    // delegates
    // delegators
    public Lexer[] getDelegates() {
        return new Lexer[] {};
    }

    public HtmlDocLexer() {} 
    public HtmlDocLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public HtmlDocLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);
    }
    public String getGrammarFileName() { return "/Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g"; }

    // $ANTLR start "BODY"
    public final void mBODY() throws RecognitionException {
        try {
            int _type = BODY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:6:6: ( 'body' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:6:8: 'body'
            {
            match("body"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "BODY"

    // $ANTLR start "DOC"
    public final void mDOC() throws RecognitionException {
        try {
            int _type = DOC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:7:5: ( 'doc' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:7:7: 'doc'
            {
            match("doc"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "DOC"

    // $ANTLR start "TITLE"
    public final void mTITLE() throws RecognitionException {
        try {
            int _type = TITLE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:8:7: ( 'title' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:8:9: 'title'
            {
            match("title"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "TITLE"

    // $ANTLR start "T__8"
    public final void mT__8() throws RecognitionException {
        try {
            int _type = T__8;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:9:6: ( '</body>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:9:8: '</body>'
            {
            match("</body>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__8"

    // $ANTLR start "T__9"
    public final void mT__9() throws RecognitionException {
        try {
            int _type = T__9;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:10:6: ( '</html>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:10:8: '</html>'
            {
            match("</html>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__9"

    // $ANTLR start "T__10"
    public final void mT__10() throws RecognitionException {
        try {
            int _type = T__10;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:11:7: ( '</title>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:11:9: '</title>'
            {
            match("</title>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__10"

    // $ANTLR start "T__11"
    public final void mT__11() throws RecognitionException {
        try {
            int _type = T__11;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:12:7: ( '<body>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:12:9: '<body>'
            {
            match("<body>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__11"

    // $ANTLR start "T__12"
    public final void mT__12() throws RecognitionException {
        try {
            int _type = T__12;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:13:7: ( '<html>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:13:9: '<html>'
            {
            match("<html>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__12"

    // $ANTLR start "T__13"
    public final void mT__13() throws RecognitionException {
        try {
            int _type = T__13;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:14:7: ( '<title>' )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:14:9: '<title>'
            {
            match("<title>"); 



            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "T__13"

    // $ANTLR start "TEXT"
    public final void mTEXT() throws RecognitionException {
        try {
            int _type = TEXT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:26:6: ( (~ ( '<' ) )* )
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:26:8: (~ ( '<' ) )*
            {
            // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:26:8: (~ ( '<' ) )*
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( ((LA1_0 >= '\u0000' && LA1_0 <= ';')||(LA1_0 >= '=' && LA1_0 <= '\uFFFF')) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:
            	    {
            	    if ( (input.LA(1) >= '\u0000' && input.LA(1) <= ';')||(input.LA(1) >= '=' && input.LA(1) <= '\uFFFF') ) {
            	        input.consume();
            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;
            	    }


            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        	// do for sure before leaving
        }
    }
    // $ANTLR end "TEXT"

    public void mTokens() throws RecognitionException {
        // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:8: ( BODY | DOC | TITLE | T__8 | T__9 | T__10 | T__11 | T__12 | T__13 | TEXT )
        int alt2=10;
        switch ( input.LA(1) ) {
        case 'b':
            {
            int LA2_1 = input.LA(2);

            if ( (LA2_1=='o') ) {
                int LA2_6 = input.LA(3);

                if ( (LA2_6=='d') ) {
                    int LA2_13 = input.LA(4);

                    if ( (LA2_13=='y') ) {
                        int LA2_19 = input.LA(5);

                        if ( ((LA2_19 >= '\u0000' && LA2_19 <= ';')||(LA2_19 >= '=' && LA2_19 <= '\uFFFF')) ) {
                            alt2=10;
                        }
                        else {
                            alt2=1;
                        }
                    }
                    else {
                        alt2=10;
                    }
                }
                else {
                    alt2=10;
                }
            }
            else {
                alt2=10;
            }
            }
            break;
        case 'd':
            {
            int LA2_2 = input.LA(2);

            if ( (LA2_2=='o') ) {
                int LA2_7 = input.LA(3);

                if ( (LA2_7=='c') ) {
                    int LA2_14 = input.LA(4);

                    if ( ((LA2_14 >= '\u0000' && LA2_14 <= ';')||(LA2_14 >= '=' && LA2_14 <= '\uFFFF')) ) {
                        alt2=10;
                    }
                    else {
                        alt2=2;
                    }
                }
                else {
                    alt2=10;
                }
            }
            else {
                alt2=10;
            }
            }
            break;
        case 't':
            {
            int LA2_3 = input.LA(2);

            if ( (LA2_3=='i') ) {
                int LA2_8 = input.LA(3);

                if ( (LA2_8=='t') ) {
                    int LA2_15 = input.LA(4);

                    if ( (LA2_15=='l') ) {
                        int LA2_21 = input.LA(5);

                        if ( (LA2_21=='e') ) {
                            int LA2_23 = input.LA(6);

                            if ( ((LA2_23 >= '\u0000' && LA2_23 <= ';')||(LA2_23 >= '=' && LA2_23 <= '\uFFFF')) ) {
                                alt2=10;
                            }
                            else {
                                alt2=3;
                            }
                        }
                        else {
                            alt2=10;
                        }
                    }
                    else {
                        alt2=10;
                    }
                }
                else {
                    alt2=10;
                }
            }
            else {
                alt2=10;
            }
            }
            break;
        case '<':
            {
            switch ( input.LA(2) ) {
            case '/':
                {
                switch ( input.LA(3) ) {
                case 'b':
                    {
                    alt2=4;
                    }
                    break;
                case 'h':
                    {
                    alt2=5;
                    }
                    break;
                case 't':
                    {
                    alt2=6;
                    }
                    break;
                default:
                    NoViableAltException nvae =
                        new NoViableAltException("", 2, 9, input);

                    throw nvae;

                }

                }
                break;
            case 'b':
                {
                alt2=7;
                }
                break;
            case 'h':
                {
                alt2=8;
                }
                break;
            case 't':
                {
                alt2=9;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 4, input);

                throw nvae;

            }

            }
            break;
        default:
            alt2=10;
        }

        switch (alt2) {
            case 1 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:10: BODY
                {
                mBODY(); 


                }
                break;
            case 2 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:15: DOC
                {
                mDOC(); 


                }
                break;
            case 3 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:19: TITLE
                {
                mTITLE(); 


                }
                break;
            case 4 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:25: T__8
                {
                mT__8(); 


                }
                break;
            case 5 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:30: T__9
                {
                mT__9(); 


                }
                break;
            case 6 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:35: T__10
                {
                mT__10(); 


                }
                break;
            case 7 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:41: T__11
                {
                mT__11(); 


                }
                break;
            case 8 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:47: T__12
                {
                mT__12(); 


                }
                break;
            case 9 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:53: T__13
                {
                mT__13(); 


                }
                break;
            case 10 :
                // /Users/pelle/itu/eclipse_workspace_37_advanced_models/antlr_htmldoc/src/dk/itu/htmldoc/HtmlDoc.g:1:59: TEXT
                {
                mTEXT(); 


                }
                break;

        }

    }


 

}