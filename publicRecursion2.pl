
test_genN(N) :- findall(R, genN(N,R), Out), write(Out), nl.

public_genN:-
        write('% public_genN'),nl,
	test_genN(2),
	test_genN(3).

test_genXY(N) :- findall(R, genXY(N,R), Out), write(Out), nl.

public_genXY :-
        write('% public_genXY'),nl,
	test_genXY(2),
	test_genXY(3).

test_flat(L) :- findall(R, flat(L,R), Out), write(Out), nl.

public_flat :-
        write('% public_flat'),nl,
	test_flat([[1],[2,3]]),
	test_flat([1,[2,3]]),
	test_flat([[1,[2]],3]),
	test_flat([[3],[2],[1]]).
