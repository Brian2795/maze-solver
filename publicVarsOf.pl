
% Uncomment following line to automatically include logic.pl
% :- initialization(['logic.pl']).

testVarsOf([]).
testVarsOf([F|T]) :- 
	write(F), 
	write(' = '),
	findall(C,varsOf(F,C),R),
	sort(R,R1),
	writeln(R1), 
	testVarsOf(T). 

public_varsOf :- 
    writeln('% public_varsOf'),
	formulaList(L),
	testVarsOf(L).

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