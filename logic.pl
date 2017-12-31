/*---------------------------------------------------------------

    CMSC 330 Project 6 - Maze Solver and SAT in Prolog

    NAME: Jung S. Lee

*/

% swipl
% halt
% ['logic']

%%%%%%%%%%%%%%%%%%%%%%
% Part 1 - Recursion %
%%%%%%%%%%%%%%%%%%%%%%

% ackermann - M and N are the two arguments, and R is the result. Cf http://mathworld.wolfram.com/AckermannFunction.html for the definition of the ackermann function

ackermann(0,N,R) :- R is N+1,!.
ackermann(M,0,R) :- M2 is M-1, ackermann(M2,1,R),!.
ackermann(M,N,R) :- N2 is N-1, ackermann(M,N2,R2), M2 is M-1, ackermann(M2,R2,R),!.


% sum - R is sum of entries in list L

sum([],1).
sum([H|T],R) :-
    sum(T,R2),
    R is H+R2.


% prod - R is product of entries in list L

prod([],1).
prod([H|T],R) :-
    prod(T,R2),
    R is H*R2.


% fill - R is list of N copies of X

fill(0,_,[]) :- !.

fill(N,X,[H|T]) :-
    N1 is N-1,
    X = H,
    fill(N1,X,T),!.

fill(N,X,R) :-
    N2 is N-1,
    fill(N2,X,R2),
    R = [X|R2],!.


% genN - R is value between 0 and N-1, in order

genN(N,R) :-
    N > 0,
    N1 is N-1,
    (genN(N1,R);
    R is N1).


% genXY - R is pair of values [X,Y] between 0 and N-1, in lexicographic order

genXY(N,R) :-
    genN(N,R1),
    genN(N,R2),
    R = [R1,R2].


% flat(L,R) - R is elements of L concatentated together, in order

flat([],[]).
flat([H|T],R) :-
    flat(T,R1),
    (integer(H) ->
        append([H],R1,R);
        append(H,R1,R)).


% is_prime(P) - P is an integer; predicate is true if P is prime.

is_prime(2).
is_prime(3).
is_prime(P) :- R is floor(sqrt(P)), primeHelper(2,R,P).

primeHelper(N,R,P) :-
    N > R -> true;
        (0 is mod(P,N) -> false;
            N2 is N+1, primeHelper(N2,R,P)).


% removes the first N elements of list L

remove_lang(L,0,L).
remove_lang([_|T],N,R) :-
    N1 is N-1,
    remove_lang(T,N1,R).


% counts how many instances of char S precede list L

count_lang(_,[],0).
count_lang(S,[H|T],N) :-
    H = S ->
        count_lang(S,T,N1),
        N is N1+1;
        N = 0.


% in_lang(L) - L is a list of atoms a and b; predicate is true L is in the language accepted by the following CFG:
/*    
CFG 
S -> T | V
T -> UU
U -> aUb | ab
V -> aVb | aWb
W -> bWa | ba
*/

in_lang(L) :-
    count_lang(a,L,A1),
    remove_lang(L,A1,L2),
    count_lang(b,L2,B1),
    remove_lang(L2,B1,L3),
    count_lang(a,L3,A2),
    remove_lang(L3,A2,L4),
    count_lang(b,L4,B2),
    remove_lang(L4,B2,L5),
    L5 = [],
    A1 > 0,
    A2 > 0,
    (
        (A1 = B1, A2 = B2);
        (A1 = B2, A2 = B1)
    ),!.


%%%%%%%%%%%%%%%%%%%%%%%%
% Part 2 - Maze Solver %
%%%%%%%%%%%%%%%%%%%%%%%%

% counter(S,L,N) - counter returns the number of instances N of char S in list L

counter(_,[],0).
counter(S,[H|T],N) :-
    counter(S,T,N1),
    (S = H ->
        N is N1+1;
        N is N1).


% stats(U,D,L,R) - number of cells w/ openings up, down, left, right
 
stats(U,D,L,R) :-
    maze(N,_,_,_,_),
    findall(P,genXY(N,P),Ps),
    statsHelper(Ps,U,D,R,L),
    U = D,
    L = R.

statsHelper([],0,0,0,0).
statsHelper([[X,Y]|T],U,D,R,L) :-
    cell(X,Y,Dirs,_),
    counter(u,Dirs,U1),
    counter(d,Dirs,D1),
    counter(r,Dirs,R1),
    counter(l,Dirs,L1),
    statsHelper(T,U2,D2,R2,L2),
    U is U1+U2,
    D is D1+D2,
    R is R1+R2,
    L is L1+L2.


% indexElem(S,L1,L2,N) - returns the element N of list L2 at the same index of char S in list L2

indexElem(S,[H1|T1],[H2|T2],N) :-
    H1 = S ->
        N = H2;
        indexElem(S,T1,T2,N).


% pathFinder(X,Y,Dirs,W) - computes weight W of traveling from point X,Y through directions Dirs

pathFinder(_,_,[],0).
pathFinder(X,Y,[H|T],W) :-
    cell(X,Y,Ds,Ws),
    indexElem(H,Ds,Ws,W1),
    (H = u -> X1 is X, Y1 is Y-1;
        (H = d -> X1 is X, Y1 is Y+1;
            (H = r -> X1 is X+1, Y1 is Y;
                (H = l -> X1 is X-1, Y1 is Y; false)))),
    pathFinder(X1,Y1,T,W2),
    W is W1+W2.


% validPath(N,W) - W is weight of valid path N rounded to 4 decimal places

validPath(N,W) :-
    path(N,SX,SY,Dirs),
    pathFinder(SX,SY,Dirs,W1),
    round4(W1,W).

round4(X,Y) :- T1 is X*10000, T2 is round(T1), Y is T2/10000.


% step(X,Y,D,L) - returns list L of coordinates that are reachable with one step from coordinate X Y given directions D

step(_,_,[],[]).
step(X,Y,[H|T],L) :-
    (H = u -> X1 is X, Y1 is Y-1;
        (H = d -> X1 is X, Y1 is Y+1;
            (H = r -> X1 is X+1, Y1 is Y;
                (H = l -> X1 is X-1, Y1 is Y; false)))),
    C1 = [X1,Y1],
    step(X,Y,T,C2),
    L = [C1|C2].


% steps(L1,L2) - given list of coordinates L1, appends to a list L3 of reachable coordinates with one step 

steps([],[]).
steps([[X,Y]|T],L) :-
    cell(X,Y,Dirs,_),
    step(X,Y,Dirs,L1),
    steps(T,L2),
    append(L1,L2,L).
      

% distinct(Q,V,A) - returns all members of Q that are not in V

distinct([],V,[]).
distinct([H|T],V,A) :-
    (member(H,V) -> distinct(T,V,A);
    distinct(T,V,A1),
    A = [H|A1]).

%  unique(L1,L2) - returns a version of L1 without repeated elements

unique([],[]).
unique([H],[H]).
unique([H1,H2|T],L2) :-
    (H1 = H2 -> unique([H2|T],L2);
        unique([H2|T],L),
        L2 = [H1|L]).

% clean(L1,L2) - returns sorted and unique L2 of L1

clean([],[]).
clean(L1,L2) :-
    sort(L1,L3),
    unique(L3,L2).


% layer(Dist,Queue,Visited,Ans) - processes the layers of steps given cells Visited, cells in Queue, and current Dist
    
layer(_,[],_,[]).
layer(D,Q,V,L) :-
    A1 = [D,Q],
    D1 is D+1,
    steps(Q,Qn),
    distinct(Qn,V,Qn2),
    clean(Qn2,Qn3),
    append(Qn3,V,V1),
    sort(V1,V2),
    layer(D1,Qn3,V2,A2),
    L = [A1|A2],!.
    

% findDistance(L) - L is list of coordinates of cells at distance D from start

findDistance(L) :-
    maze(_,SX,SY,_,_),
    Q = [[SX,SY]],
    V = [[SX,SY]],
    layer(0,Q,V,L).


% solve - True if maze is solvable, fails otherwise.

solve :-
    maze(_,_,_,EX,EY),
    findDistance(L1),
    flat(L1,L2),
    flat(L2,L3),
    member([EX,EY],L3).


%%%%%%%%%%%%%%%%
% Part 3 - SAT %
%%%%%%%%%%%%%%%%



% eval(F,A,R) - R is t if formula F evaluated with list of 
%                 true variables A is true, false otherwise

eval(F,A,R) :-
    F(A) -> R is true; R is false.

% varsOf(F,R) - R is list of free variables in formula F

varsOf(F,R) :- fail.

% sat(F,R) - R is a list of true variables that satisfies F

sat(F,R) :- fail.

% Helper Function
% subset(L, R) - R is a subset of list L, with relative order preserved

subset([], []).
subset([H|T], [H|NewT]) :- subset(T, NewT).
subset([_|T], NewT) :- subset(T, NewT).

