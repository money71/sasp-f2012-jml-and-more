// NB! its a really simple grammer even not head tag and doesn't work with line breaks...
grammar HtmlDoc;
options { output=AST; }
tokens {
	DOC='doc';
	TITLE='title';
	BODY='body';
}

@header {
  package dk.itu.htmldoc;
}
@lexer::header {
  package dk.itu.htmldoc;
}

html_doc
	: '<html>' html_header html_body '</html>' -> ^('doc' html_header html_body);

html_header
	: '<title>' TEXT '</title>' -> ^('title' TEXT) ;

html_body
	: '<body>' TEXT '</body>' -> ^('body' TEXT)	;

TEXT : (~('<'))*;