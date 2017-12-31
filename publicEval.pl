
% Uncomment following line to automatically include logic.pl
% :- initialization(['logic.pl']).

testEval([],_).
testEval([H|T],A) :- 
	nl,
	testEval2(H,A),
	testEval(T,A).

testEval2(_,[]).
testEval2(F,[H|T]) :- 
	write(F), 
	write(' '),
	write(H), 
	write(' = '),
	findall(C,eval(F,H,C),R),
	writeln(R), 
	testEval2(F,T), !. 

public_eval :- 
    writeln('% public_eval'),
	formulaList(F),
	assignmentList(A),
	testEval(F,A).

formulaList([
        t,
        f,
        x,
        [and, x, y],
        [or, y, x],
        [no, x]
	  ]).

assignmentList([
        [],
        [x]
	  ]).
