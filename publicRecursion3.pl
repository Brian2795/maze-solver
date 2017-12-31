test_isprime(N) :-
    is_prime(N), !, write(N), write(' is prime'), nl.
test_isprime(N) :-
    \+is_prime(N), !, write(N), write(' is NOT prime'), nl.

public_isprime:-
        write('% public_isprime'),nl,
	test_isprime(3),
	test_isprime(4),
	test_isprime(31).

test_inlang(L) :-
    in_lang(L), !, write(L), write(' is in lang'), nl.
test_inlang(L) :-
    \+in_lang(L), !, write(L), write(' is NOT in lang'), nl.

public_inlang :-
        write('% public_inlang'),nl,
	test_inlang([a,a,b,b,a,b]),
	test_inlang([a,a,a,b,b,a,a,b,b,b]),
	test_inlang([a,a,a,b,b,a,b,b,b]).
