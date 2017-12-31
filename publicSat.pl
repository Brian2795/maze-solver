
% Uncomment following line to automatically include logic.pl
% :- initialization(['logic.pl']).

testSat([]).
testSat([F|T]) :- 
	write(F), 
	write(' = '),
	findall(C,sat(F,C),R),
	sort(R,R1),
	writeln(R1), 
	testSat(T). 

public_sat :- 
    writeln('% public_sat'),
	formulaList(F),
	testSat(F).

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