% clpfd_smt_base:to_smtlib(maplist(all_distinct, [[X,Y,1,2,a], [a,s,d,f,g]])).
% => clpfd_smt_base:smt_constraint(X,Y).
% X = all_distinct(a,s,d,f,g),
% Y = [] ? ;
% X = all_distinct(_A,_B,1,2,a),
% Y = ['VAR'('_905'),'VAR'('_945')] ? ;
% no