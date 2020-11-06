:- module(printer_ext, [
                            write_string_to_stream/2, 
                            newline/1, 
                            writes/1
                         ]).


/**********************************************************************************************
 * write_string_to_stream(+Stream, +String)
 * 
 * Strings in Sicstus are Lists of Codes. 
 * More About I/O: 
 *  https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/mpg_002dtop_002dcio.html
 * 
 * Example: 
 *  open('test.txt', write, Out), 
 *  append("abc\n", "def", L),
 *  write_string_to_stream(Out, L),
 *  close(Out).
**********************************************************************************************/
write_string_to_stream(_Stream, []) :- !.
write_string_to_stream(Stream, [Code|Tail]) :-
    put_code(Stream, Code),
    write_string_to_stream(Stream, Tail).


/* During development nl(+Out) did not work. */
newline(Stream) :-
    put_code(Stream, 10).


/* Just a simple codelist to console print command. */
writes([]) :- !.
writes([Code|Tail]) :- 
    put_code(Code), writes(Tail).


/*
    Sicstus doesn't have a flatten predicate. 
    Use append(ListOfLists, FlatList) instead.
*/