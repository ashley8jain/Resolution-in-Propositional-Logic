datatype Prop = TOP                   | BOTTOM
                     | ATOM of string     | NOT of Prop
                     | AND of Prop * Prop | OR of Prop * Prop 
                     | IMP of Prop * Prop | IFF of Prop * Prop
                     | ITE of Prop * Prop * Prop;

datatype Lit = P of string | N of string | TOPL | BOTTOML
datatype Clause = CLS of (Lit list);
datatype Cnf = CNF of (Clause list);


signature AST = 

sig
    val toPrefix  : Prop -> string
    val toPostfix : Prop -> string
    val isEqual   : Prop -> Prop -> bool
    (*val make2cnf : Prop -> Prop*)
    val makeCnf   : Prop -> Cnf
    val resolve   : Cnf -> bool
    (*val checking : Cnf -> Lit  list list*)
end;

structure AS:AST = 
struct
    fun toPrefix (TOP)  = "TRUE" |
        toPrefix (BOTTOM) = "FALSE" |
        toPrefix(NOT(P1)) = "NOT(" ^ toPrefix(P1)^")" |
        toPrefix(ATOM(b)) = b |
        toPrefix(AND(P1,P2)) = "AND(" ^ toPrefix(P1) ^ "," ^ toPrefix(P2)^")" |
        toPrefix(IMP(P1,P2)) = "IFTHEN(" ^ toPrefix(P1) ^ "," ^ toPrefix(P2)^")" |
        toPrefix(OR(P1,P2)) = "OR(" ^ toPrefix(P1) ^ "," ^ toPrefix(P2)^")" |
        toPrefix(IFF(P1,P2)) = "IFF(" ^ toPrefix(P1) ^ "," ^ toPrefix(P2)^")" |
        toPrefix(ITE(P1,P2,P3)) = "IFTHENELSE(" ^ toPrefix(P1) ^ "," ^ toPrefix(P2) ^ "," ^ toPrefix(P3)^")";


    fun toPostfix(TOP)  = "TRUE" |
        toPostfix(BOTTOM) = "FALSE" |
        toPostfix(NOT(P1)) = "("^toPostfix(P1) ^ ")NOT"  |
        toPostfix(ATOM(b)) = b |
        toPostfix(AND(P1,P2)) =  "("^toPostfix(P1) ^ " " ^ toPostfix(P2) ^  ")AND"|
        toPostfix(IMP(P1,P2)) =  "("^toPostfix(P1) ^ " " ^ toPostfix(P2) ^ ")IFTHEN" |
        toPostfix(OR(P1,P2)) =  "("^toPostfix(P1) ^ " " ^ toPostfix(P2) ^ ")OR"|
        toPostfix(IFF(P1,P2)) = "("^toPostfix(P1) ^ " " ^ toPostfix(P2) ^ ")IFF" |
        toPostfix(ITE(P1,P2,P3)) =  "("^toPostfix(P1) ^ " " ^ toPostfix(P2) ^ " " ^ toPostfix(P3) ^ ")IFTHENELSE";

    fun isEqual P1 P2 = false;




    fun NotAndOr(TOP) = TOP | NotAndOr(BOTTOM) = BOTTOM |
        NotAndOr(ATOM(b)) = ATOM(b) |
        NotAndOr(NOT(P1)) = NOT(NotAndOr(P1)) |
        NotAndOr(AND(P1,P2)) = AND(NotAndOr(P1),NotAndOr(P2)) |
        NotAndOr(OR(P1,P2)) = OR(NotAndOr(P1),NotAndOr(P2)) |
        NotAndOr(IMP(P1,P2)) = OR(NOT(NotAndOr(P1)),NotAndOr(P2)) |
        NotAndOr(IFF(P1,P2)) = AND(OR(NOT(NotAndOr(P1)),NotAndOr(P2)),OR(NotAndOr(P1),NOT(NotAndOr(P2)))) |
        NotAndOr(ITE(P1,P2,P3)) = OR( AND(NotAndOr(P1),NotAndOr(P2)) , AND(NOT(NotAndOr(P1)),NotAndOr(P3)) );

    fun NNF(TOP) = TOP | NNF(BOTTOM) = BOTTOM |
        NNF(ATOM(b)) = ATOM(b) |
        NNF(NOT(ATOM(b))) = NOT(ATOM(b)) |
        NNF(NOT(NOT(P1))) = NNF(P1) |
        NNF(NOT(AND(P1,P2))) = OR(NNF(NOT(P1)),NNF(NOT(P2))) |
        NNF(NOT(OR(P1,P2))) = AND(NNF(NOT(P1)),NNF(NOT(P2))) |
        NNF(OR(P1,P2)) = OR(NNF(P1),NNF(P2)) |
        NNF(AND(P1,P2)) = AND(NNF(P1),NNF(P2));

    fun distribOverOR(AND(P1,P2),P3) = AND(distribOverOR(P1,P3),distribOverOR(P2,P3)) |
        distribOverOR(P1,AND(P2,P3)) = AND(distribOverOR(P1,P2),distribOverOR(P1,P3)) |
        distribOverOR(P1,P2) = OR(P1,P2)

    fun CNF_prop(AND(P1,P2)) = AND(CNF_prop(P1),CNF_prop(P2)) |
        CNF_prop(OR(P1,P2)) = distribOverOR(CNF_prop(P1),CNF_prop(P2)) |
        CNF_prop(P1) = P1

    fun make2cnf(P1) = CNF_prop(NNF(NotAndOr(P1)))

    fun makeClauseList(OR(P1,P2)) = makeClauseList(P1) @ makeClauseList(P2) |
        makeClauseList(NOT(ATOM(b))) = [N(b)] |
        makeClauseList(ATOM(b)) = [P(b)] |
        makeClauseList(TOP) = [TOPL] |
        makeClauseList(BOTTOM) = [BOTTOML]

    fun make3cnf(AND(P1,P2)) = make3cnf(P1) @ make3cnf(P2) |
        make3cnf(P1) = [CLS(makeClauseList(P1))]

    fun makeCnf(P1) = CNF(make3cnf(make2cnf(P1)))







    fun litSort(P(a),P(b)) = a<b |
        litSort(P(a),N(b)) = true |
        litSort(N(a),P(b)) = false |
        litSort(N(a),N(b)) = a<b

    fun clauseSort([],b) = true |
        clauseSort(a,[]) = false |
        clauseSort(hd1::tl1,hd2::tl2) = if(hd1=hd2) then clauseSort(tl1,tl2) else litSort(hd1,hd2)

    fun mergeSort R [] = [] |
        mergeSort R [a] = [a] |
        mergeSort R L = 
        let
            fun split([]) = ([],[]) |
                split([a]) = ([a],[]) |
                split(hd1::hd2::tl) = 
                let
                    val (le,ri) = split tl
                in
                    (hd1::le,hd2::ri)
                end;
            val (left,right) = split L;
            val sortLeft = mergeSort R left;
            val sortRight = mergeSort R right;

            fun merge([],[],_) = [] |
                merge([],L2,_) = L2 |
                merge(L1,[],_) = L1 |             (*sort with removing duplicate*)
                merge(hd1::tl1,hd2::tl2,R) = if(hd1=hd2) then merge(tl1,hd2::tl2,R)
                                             else if R(hd1,hd2) then hd1::(merge(tl1,hd2::tl2,R))
                                             else hd2::(merge(hd1::tl1,tl2,R))
        in
            merge(sortLeft,sortRight,R)
        end

    fun listlist([]) = [] |
        listlist([CLS(a)]) = [a] |
        listlist(CLS(a)::tl) = a::listlist(tl);

    fun sort(CL) = let val LL = listlist(CL);
                       val sortedClauses = map (mergeSort litSort) LL;
                    in (mergeSort clauseSort sortedClauses)
                    end

    fun sort2(LL) = let val sortedClauses = map (mergeSort litSort) LL;
                    in (mergeSort clauseSort sortedClauses)
                    end



    fun lookup(a,[]) = false | 
        lookup(a,hd::tl) = if(a=hd) then true else lookup(a,tl) 

    fun clean1up(LL) = let fun checkSuperSet([],sub) = false |
                               checkSuperSet(super,[]) = true |
                               checkSuperSet(super,hd::tl) = if(lookup(hd,super)) then checkSuperSet(super,tl) else false
                           fun isSuperSet(a,[b]) = checkSuperSet(a,b) |
                               isSuperSet(a,hd::tl) = if(checkSuperSet(a,hd)) then true else isSuperSet(a,tl)
                           fun clean1up_helper([])=[] |
                               clean1up_helper([a]) = [a] | 
                               clean1up_helper(hd::tl) = if(isSuperSet(hd,tl)) then clean1up_helper(tl) else hd::clean1up_helper(tl);
                           fun customComparator(L1,L2) = List.length(L1)>List.length(L2)
                           val orderedLL = mergeSort customComparator LL
                       in clean1up_helper(orderedLL)
                       end

    fun clean2up([]) = [] |
        clean2up(hd::tl) = let fun existsComp((cls)) = let fun isComp(P(a),N(b)) = (a=b) |
                                                               isComp(N(a),P(b)) = (a=b) |
                                                               isComp(_,_) = false
                                                           fun checkComp(literal,[]) = false |
                                                               checkComp(literal,hd::tl) = if(isComp(literal,hd)) then true else checkComp(literal,tl)
                                                           fun exists2Comp([]) = false |
                                                               exists2Comp(hd::tl) = if(checkComp(hd,tl)) then true else exists2Comp(tl)
                                                        in exists2Comp(cls)
                                                        end
                           in if(existsComp(hd)) then clean2up(tl) else hd::clean2up(tl)
                           end
    fun delLitl_L([],Litl)= [] |
        delLitl_L(hd::tl,Litl) = if(hd=Litl) then delLitl_L(tl,Litl) else hd::delLitl_L(tl,Litl)

    fun clean3up([]) = [] |
        clean3up(hd::tl) = if(lookup(TOPL,hd)) then clean3up(tl) else if(lookup(BOTTOML,hd)) then delLitl_L(hd,BOTTOML)::clean3up(tl) else hd::clean3up(tl)

    fun cleanup_CL(cnf) = clean2up(clean1up(sort(cnf)))
    fun cleanup_LL(LL) = clean2up(clean1up(sort2(LL)))

    fun neg(P(a)) = N(a) |
        neg(N(a)) = P(a)        

    

    fun delList_LL(_,[])=[] |
        delList_LL([],M)=M  |
        delList_LL(x::L, M) = delList_LL(L,delLitl_L(M,x))

    (*fun resolve(CNF(cnf)) = clean3up(listlist(cnf))*)
    fun resolve(CNF(cnf)) = let fun atoms_l([]) = [] |
                                    atoms_l(P(a)::tl) = P(a)::atoms_l(tl) |
                                    atoms_l(N(a)::tl) = P(a)::atoms_l(tl)
                                fun atoms_ll([]) = [] |
                                    atoms_ll(hd::tl) = atoms_l(hd)@atoms_ll(tl)
                                fun list_atoms([]) = [] |
                                    list_atoms(LL) = mergeSort litSort (atoms_ll(LL))

                                fun resolvent_atom([],atom) = [] |
                                    resolvent_atom(LL,atom) = let fun LL_withAtom([],atom) = [] |
                                                                       LL_withAtom(hd::tl,atom) = if(lookup(atom,hd)) then hd::(LL_withAtom(tl,atom)) else (LL_withAtom(tl,atom))
                                                                   fun resolution([],V_bar,atom)  = [] |
                                                                       resolution(hd::tl,V_bar,atom) = let fun res_helper(L,[],atom) = [L] |
                                                                                                               res_helper(L,hd::tl,atom) = let val D_i = (delLitl_L(L,atom)@delLitl_L(hd,neg(atom)))
                                                                                                                                           in  [D_i]@res_helper(L,tl,atom)
                                                                                                                                           end
                                                                                                           val resolution_done = res_helper(hd,V_bar,atom)
                                                                                                       in resolution_done@resolution(tl,V_bar,atom)
                                                                                                       end
                                                                   fun resolving_LL(LL,V,V_bar,atom) = let val rem_LL = delList_LL(V_bar,delList_LL(V,LL))
                                                                                                           val D = resolution(V,V_bar,atom)
                                                                                                       in cleanup_LL(D@rem_LL)
                                                                                                       end
                                                                   val V = LL_withAtom(LL,atom)
                                                                   val V_bar = LL_withAtom(LL,neg(atom))
                                                            in if(V=[] orelse V_bar=[])  then LL else resolving_LL(LL,V,V_bar,atom)
                                                            end

                                fun resolvent_atoms([],LL) = LL |
                                    resolvent_atoms(hd::tl,LL) = resolvent_atoms(tl,resolvent_atom(LL,hd))
                                fun resolve_helper([]) = true |
                                    resolve_helper([a]) = if a=[] then false else true |
                                    resolve_helper(LL) = if (resolvent_atoms(list_atoms(LL),LL))=[[]] then false else true
                                (*fun resolve_helper([]) = [] |
                                    resolve_helper([a]) = [a] |
                                    resolve_helper(LL) = resolvent_atoms(list_atoms(LL),LL)*)

                            in resolve_helper(cleanup_LL(clean3up(listlist(cnf))))
                            end
                            

    (*fun checking(CNF(cnf)) = resolvent_atom(hd(list_atoms(cleanup_CL(cnf))),(cleanup_CL(cnf)))*)
        (*let val L1 = LL_withAtom(hd(list_atoms(cleanup_CL(cnf))),(cleanup_CL(cnf)))
                                val L2 = LL_withAtom(neg(hd(list_atoms(cleanup_CL(cnf)))),(cleanup_CL(cnf)))
                            in  (sort2(resolution(L1,L2,hd(list_atoms(cleanup_CL(cnf))))))
                            end*)
 

end;

(*print(AS.toPrefix(AS.makeCnf( IFF( ATOM("do"),ATOM("there is try") ))));*)
(*print(AS.toPrefix(AS.makeCnf( NOT( ATOM("fes") ) )));*)

(*print(AS.toPrefix(NOT(TOP)));
print(AS.toPrefix(NOT(BOTTOM)));*)

(*AS.toPrefix(AS.make2cnf( IFF( ATOM("a"),IFF(ATOM("b"),ATOM("c")) )));*)
AS.resolve(AS.makeCnf( AND( OR(ATOM("c"),OR(ATOM("a"),ATOM("a"))) , OR(OR(ATOM("a"),ATOM("b")),ATOM("c")) )));

AS.makeCnf( IFF( ATOM("a"),IFF(ATOM("b"),ATOM("c"))));
AS.resolve(AS.makeCnf( IFF( ATOM("a"),IFF(ATOM("b"),ATOM("c")))));

AS.resolve(AS.makeCnf( AND(ATOM("b"),NOT(ATOM("b"))) ));
AS.resolve(AS.makeCnf( AND(OR(ATOM("a"),ATOM("b")),OR(ATOM("a"),NOT(ATOM("b")))) ));

AS.resolve(AS.makeCnf( IFF( ATOM("a"),ATOM("b") )));
AS.resolve(AS.makeCnf( AND(ATOM("p"),AND(ATOM("q"),NOT(ATOM("p")))) ));
AS.resolve(AS.makeCnf( AND(ATOM("p"),AND(ATOM("q"),OR(NOT(ATOM("p")),NOT(ATOM("q"))))) ));
AS.resolve(AS.makeCnf( AND(NOT(ATOM("p")),AND(OR(ATOM("p"),ATOM("r")),OR(ATOM("p"),ATOM("q")))) ));
AS.resolve(AS.makeCnf( AND(OR(ATOM("p"),OR(NOT(ATOM("q")),NOT(ATOM("r")))),AND(NOT(ATOM("p")),AND(OR(ATOM("p"),ATOM("r")),OR(ATOM("p"),ATOM("q"))))) ));

AS.resolve(AS.makeCnf( AND(OR(BOTTOM,ATOM("a")),TOP) ))

