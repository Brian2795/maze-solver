:- initialization(
    [ 'logic.pl'
    , 'publicRecursion1.pl'
    , 'publicRecursion2.pl'
    , 'publicRecursion3.pl'
    , 'publicMaze1.pl'
    , 'publicMaze2.pl'
%    , 'publicEval.pl'
%   , 'publicVarsOf.pl'
%    , 'publicSat.pl'
    ]).
run_f(Func) :-
    % name(Func,FunName),
    % writef("Testcase: %s\n",[FunName]),
    Func.
testcases(
    [ public_prod
    , public_ackermann
    , public_isprime
    , public_fill
    , public_genN
    , public_genXY
    , public_flat
    , public_inlang
    , public_stats
    , public_validPath
    , public_findDistance
    , public_solve
%    , public_eval
%    , public_varsOf
%    , public_sat
    ]).
run :-
    testcases(TC),
    maplist(run_f,TC).
