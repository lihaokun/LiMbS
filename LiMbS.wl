(* ::Package:: *)

BeginPackage["LiMbS`"];


GetSampleInterval::usage="GetSampleInterval";


Ps::usage="Ps";


Pr::usage="Pr";


Pc::usage="Pc";


Pos::usage="Return open sample cad projection of A.";


Pmc::usage="Return McCallum projection of A.";


polytosmt2::usage="polytosmt2";


ClauseResolve::usage="ClauseResolve";


CheckConflictHalf::usage="half conflict set check.";


Leadcoeff::usage="Leadcoeff";


FindMid::usage="findmid.";


NRASolver::usage="NRA SMT solver.";


Begin["`Private`"];


polytosmt2[f_]:=
Module[{a=Head[f],l,h,i},
    If[SameQ[a,Power],
        l={"(*"};
        h=" "<>polytosmt2[f[[1]]];
        For[i=1,i<=f[[2]],++i,AppendTo[l,h]];
        Return[StringJoin[Append[l,")"]]]
    ];
    If[SameQ[a,Plus],h="(+",
        If[SameQ[a,Times],h="(*",
            If[f<0,Return["(- "<>ToString[-f,InputForm]<>")"],
                Return[ToString[f,InputForm]],
                Return[ToString[f,InputForm]]
            ]
        ]
    ];
    l=Map[" "<>polytosmt2[#]&,f];
    l[[0]]=List;
    Return[StringJoin[{h,l,")"}]];
];


Pc[A_,x_]:=Flatten[CoefficientList[A,x]];


Pc[A_List,M_Association ,x_]:=
Module[{p1={},p2={},c,i,j},
    For[i=1,i<=Length[A],++i,
        c=CoefficientList[A[[i]],x];
        For[j=Length[c],j>0,--j,
            AppendTo[p1,c[[j]]];
            If[UnsameQ[c[[j]]/.M,0],Break[]];        
        ];
        If[SameQ[p1[[-1]]/.M,0],AppendTo[p2,A[[i]]]];            
    ];
    Return[{p1,p2}];
];


Pr[A_List,x_]:=Map[Apply[Resultant[#1,#2,x]&],Subsets[A,{2}]];


Pr[A_List,B_List,x_]:=Map[Apply[Resultant[#1,#2,x]&],Select[Tuples[{A,B}],UnsameQ[#[[1]],#[[2]]]&]];


Pmc[A_List,M_Association,x_]:=
Module[{A1,B,M1=KeyDrop[M,x],p1},
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    p1=Pc[A1,M1,x][[1]];
    A1=Select[A1,MemberQ[Variables[#/.M1],x]&];
    Return[DeleteDuplicates[Flatten[{B,p1,Discriminant[A1,x],Pr[A1,x]}]]];
];


Pmc[A_List,x_]:=
Module[{A1,B},
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    Return[DeleteDuplicates[Flatten[{B,Pc[A1,x],Discriminant[A1,x],Pr[A1,x]}]]];
];


GetSampleInterval[A_List,M_Association,x_]:=
Module[{A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]],B,A0,A2,x0=M[x],
        M1=KeyDrop[M,x],rootintervals,numroot,tmpindex,
        rightindex,rightrootindex,leftindex,leftrootindex},
    B=Select[A1,(Not[MemberQ[Variables[#],x]] && UnsameQ[Variables[#],{}])&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    A0=Select[A1,MemberQ[Variables[#/.M1],x]&];
    If[Length[A0]==0,Return[{{},{B,A1,A0,{{},{}}}}]];
    rootintervals=RootIntervals[A0/.M1];
    numroot=Length[rootintervals[[1]]];
    If[numroot==0,Return[{{},{B,A1,A0,{{},{}}}}]];
    A2=A0[[DeleteDuplicates[Flatten[rootintervals[[2]]]]]];
    tmpindex=Max[LengthWhile[rootintervals[[1]],(x0>#[[1]]|| #[[2]]==x0 )&],1];
    (*Print[rootintervals,M[x]];
    Print[tmpindex,rootintervals[[1,tmpindex]]];*)
    rightindex=rootintervals[[2,tmpindex,1]];
    rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,;;tmpindex]]];
    If[SameQ[A0[[rightindex]]/.M,0],
        Return[{{{Equal,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[rightindex]]}}}}]];
    If[x0>=rootintervals[[1,tmpindex,2]] ||  x0>Root[A0[[rightindex]]/.M1,rightrootindex],
        leftindex=rightindex;
        leftrootindex=rightrootindex;
        If[tmpindex==numroot,
            Return[{{{Greater,A0[[leftindex]],leftrootindex}},{B,A1,A0,{A2,{A0[[leftindex]]}}}}]];
        rightindex=rootintervals[[2,tmpindex+1,1]];
        rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex+1]]];
        ,
        If[tmpindex==1,
            Return[{{{Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[rightindex]]}}}}]];
        leftindex=rootintervals[[2,tmpindex-1,1]];
        leftrootindex=Plus@@Map[Count[#,leftindex]&,rootintervals[[2,1;;tmpindex-1]]];

    ];
    If[rightindex==leftindex,
        Return[{{{Greater,A0[[leftindex]],leftrootindex},
            {Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[leftindex]]}}}}],
        Return[{{{Greater,A0[[leftindex]],leftrootindex},
            {Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[leftindex]],A0[[rightindex]]}}}}]]
];


Ps[l_List,M_Association,x_]:=Module[{p1,p2,p3,M1=KeyDrop[M,x]},
    p1=Pc[l[[2]],M1,x];
    If[Length[p1[[2]]]!=0,Print[p1[[2]],M,x]];
    p2=Discriminant[l[[3]],x];
    p3=Pr[l[[4,1]],l[[4,2]],x];
    Return[DeleteDuplicates[{Sequence@@l[[1]],Sequence@@p1[[1]],Sequence@@p2,Sequence@@p3}]];
];


Pos[A_List,M_Association,x_,mod_:"Root"]:=
Module[{i,A1,B,M1,p1,p2,p3,A0,A2,x0,rootintervals,numroot,tmpindex,tmprootindex,rightindex,rightrootindex,leftindex,leftrootindex},
    Assert[mod=="Root" || mod=="poly"];
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    M1=KeyDrop[M,x];
    p1=Pc[A1,M1,x][[1]];
    p2=Discriminant[A1,x];
    A0=Select[A1,MemberQ[Variables[#/.M1],x]&];
    If[Length[A0]==0,Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],x}]];
    rootintervals=RootIntervals[A0/.M1];
    numroot=Length[rootintervals[[1]]];
    If[numroot==0,
        If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],True}]];
        If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],{}}]];
    ];
    A2=A0[[DeleteDuplicates[Flatten[rootintervals[[2]]]]]];
    tmpindex=FirstPosition[A0/.M,0,{0},1][[1]];
    If[tmpindex!=0,
        tmprootindex=0;
        For[i=1,i<=numroot && (M[x]>rootintervals[[1,i,1]] || M[x]>=rootintervals[[1,i,2]]),++i,
            tmprootindex+=Count[rootintervals[[2,i]],tmpindex]];
        If[Length[A2]>1,p3=Pr[A2,{A0[[tmpindex]]},x],p3={}];
        If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                               x==Root[A0[[tmpindex]]/.x->#&,tmprootindex]}]];
        If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                               {{Equal,A0[[tmpindex]],tmprootindex}}}]];
    ];
    (*Print[rootintervals];*)    
    tmpindex=Max[LengthWhile[rootintervals[[1]],M[x]>#[[1]]&],1];
    (*Print[tmpindex];*)    
    rightindex=rootintervals[[2,tmpindex,1]];
    rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex]]];
    x0=Root[A0[[rightindex]]/.M1,rightrootindex];
    If[M[x]<x0,
        (*Print["<"];*)
        If[tmpindex==1,
            p3=Pr[A2,{A0[[rightindex]]},x];
            If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                x<Root[A0[[rightindex]]/.(x->#)&,rightrootindex]}]];
            If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                {{Less,A0[[rightindex]],rightrootindex}}}]];
            
        ];
        leftindex=rootintervals[[2,tmpindex-1,1]];
        leftrootindex=Plus@@Map[Count[#,leftindex]&,rootintervals[[2,1;;tmpindex-1]]];
        ,
        (*Print[">"];*)
        leftindex=rightindex;
        leftrootindex=rightrootindex;
        If[tmpindex==numroot,
            p3=Pr[A2,{A0[[leftindex]]},x];
            If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                Root[A0[[leftindex]]/.(x->#)&,leftrootindex]<x}]];
            If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                {{Greater,A0[[leftindex]],leftrootindex}}}]];
        ];
        rightindex=rootintervals[[2,tmpindex+1,1]];
        rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex+1]]];
    ];
    If[rightindex==leftindex,
        p3=Pr[A2,{A0[[leftindex]]},x],
        p3=Pr[A2,{A0[[rightindex]],A0[[leftindex]]},x]];
    If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
       Root[A0[[leftindex]]/.(x->#)&,leftrootindex]<x<Root[A0[[rightindex]]/.(x->#)&,rightrootindex]}]];
    If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
       {{Greater,A0[[leftindex]],leftrootindex},
        {Less,A0[[rightindex]],rightrootindex}}}]];
];


ClauseResolve[Clause_,E_,F_]:=Union[Clause,E]/.{F->Nothing,(-F)->Nothing};


Leadcoeff[F_,x_]:=Last[CoefficientList[F,x]];


CheckConflictHalf[conflictstatelist_List,f1_,x_,l_Integer,isgreat_,isequal_]:=
Module[{isclose,rootnum,a,b,k,midcheck,skip,selectstate,status=False,rootindex,newconflictstatelist={},listindex,listlength},
    isclose=!isequal;
    If[SameQ[f1,0],
        If[isclose,Return[{False,{{-Infinity,Infinity,False,l}}}],Return[{True,conflictstatelist}]]
    ];
    rootnum=CountRoots[f1,x];
    If[rootnum==0,
        If[Not[Xor[Leadcoeff[f1,x]>0,isgreat]],
            Return[{True,conflictstatelist}],Return[{False,{{-Infinity,Infinity,False,l}}}]
        ]
    ];
    If[Not[Xor[Leadcoeff[f1,x]>0 && Mod[rootnum,2]==0 || Leadcoeff[f1,x]<0 && Mod[rootnum,2]==1 ,isgreat]],
        a=Root[f1,1];
        rootindex=2;
        If[rootindex>rootnum,b=Infinity,b=Root[f1,rootindex]];
        ,
        a=-Infinity;b=Root[f1,1];
        rootindex=1;
    ];
    skip=NestWhile[(If[#<rootnum,a=Root[f1,#+1];If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]]];#+2)&,
            #, #<=rootnum+1 && a==b&]&;
    If[!isclose, rootindex=skip[rootindex]];
    listindex=1;
    listlength=Length[conflictstatelist];
    midcheck=(status || (Length[newconflictstatelist]>0 && 
                    (#1>newconflictstatelist[[-1,2]] || 
                        #1==newconflictstatelist[[-1,2]] && !#2 && !newconflictstatelist[[-1,3]]) ||
                    Length[newconflictstatelist]==0 && #1!=-Infinity
                ))&;
    While[listindex<=listlength && rootindex<rootnum+2 ,
        If[a<conflictstatelist[[listindex,1]] ||
            (a==conflictstatelist[[listindex,1]] &&  
                ((a!=-Infinity && isclose && !conflictstatelist[[listindex,3]]) ||
                 ((a==-Infinity || isclose|| !conflictstatelist[[listindex,3]]) &&
                    (b>conflictstatelist[[listindex,2]] ||
                        (b==conflictstatelist[[listindex,2]] && 
                            (isclose|| !conflictstatelist[[listindex,3]]|| b==Infinity)
                        )
                    )
                 )
                )
            ),
            status=midcheck[a,isclose];
            AppendTo[newconflictstatelist,{a,b,isclose,l}];
            If[b==Infinity,
                Return[{status,newconflictstatelist}];
            ];
            listindex=NestWhile[#+1&,listindex,
                #<=listlength && 
                    (b>conflictstatelist[[#,2]] || 
                     (isclose || !conflictstatelist[[#,3]]) && b==conflictstatelist[[#,2]])&
            ];
            ++rootindex;++rootindex;
            If[rootindex>rootnum+1 ,Break[]];
            a=Root[f1,rootindex-1];
            If[rootindex>rootnum,b=Infinity,b=Root[f1,rootindex]];
            If[!isclose, rootindex=skip[rootindex]];
            , 
            status=midcheck[conflictstatelist[[listindex,1]],conflictstatelist[[listindex,3]]];
            AppendTo[newconflictstatelist,conflictstatelist[[listindex]]];
            If[conflictstatelist[[listindex,2]]==Infinity,
                Return[{status,newconflictstatelist}];
            ];
            k=rootindex;
            rootindex=NestWhile[(If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]];#+2)&,rootindex,
                #<=rootnum+1 && (
                    newconflictstatelist[[-1,2]]>b ||
                    (!isclose || newconflictstatelist[[-1,3]]) && b==newconflictstatelist[[-1,2]] )&
            ];
            ++listindex;
            If[rootindex>rootnum+1,Break[]];
            If[rootindex>k,a=Root[f1,rootindex-1]];
            If[isclose,rootindex=
                NestWhile[(If[#<rootnum,a=Root[f1,#+1];If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]]];#+2)&,
                  rootindex, #<=rootnum+1 && b<=newconflictstatelist[[-1,2]]&]];
            If[!isclose, rootindex=skip[rootindex]];
        ]
    ];
    If[listindex<=listlength,
        status=midcheck[conflictstatelist[[listindex,1]],conflictstatelist[[listindex,3]]];
        Scan[(status=midcheck[#[[1]],#[[3]]];AppendTo[newconflictstatelist,#])&,
            conflictstatelist[[listindex;;]]]
    ];
    If[rootindex<rootnum+2,
        status=midcheck[a,isclose];
        AppendTo[newconflictstatelist,{a,b,isclose,l}];
        Scan[(a=Root[f1,#];b=If[#>=rootnum,Infinity,Root[f1,#+1]];
                If[isclose  && b>newconflictstatelist[[-1,2]] || a!=b,
                    status=midcheck[a,isclose];
                    AppendTo[newconflictstatelist,{a,b,isclose,l}]])&,
                        Range[rootindex+1,rootnum,2]]
    ];
    If[!status && newconflictstatelist[[-1,2]]!=Infinity,status=True];
    Return[{status,newconflictstatelist}]
];


CheckConflictHalf[conflictstatelist_List,r_,l_Integer,isgreat_,isequal_]:=
Module[{isclose,status=False,index,newlist},
    isclose=!isequal;
    If[!isgreat,
        If[r==-Infinity,Return[{False,{{-Infinity,Infinity,isclose,l}}}]];
        newlist=TakeWhile[conflictstatelist,
            (#[[1]]<r || !isclose && #[[3]] && #[[1]]==r)&];
        If[Length[newlist]==0 || newlist[[-1,2]]!=Infinity, 
            AppendTo[newlist,{r,Infinity,isclose,l}]];
        
    ,
        If[r==Infinity,Return[{False,{{-Infinity,Infinity,isclose,l}}}]];
        index=LengthWhile[conflictstatelist,
            (#[[2]]<r || (isclose || !#[[3]]) && #[[2]]==r)&];
        newlist=conflictstatelist[[index+1;;]];
        If[Length[newlist]==0 || newlist[[1,1]]!=-Infinity,
            newlist={{-Infinity,r,isclose,l},Sequence@@newlist}];
    ];
    If[newlist[[1,1]]!=-Infinity || newlist[[-1,2]]!=Infinity,Return[{True,newlist}]];
    Scan[
           (If[newlist[[#-1,2]]<newlist[[#,1]] || 
                !newlist[[#,3]] && !newlist[[#-1,3]] && newlist[[#-1,2]]==newlist[[#,1]],
                status=True;Return[]])&,Range[2,Length[newlist]]];
    Return[{status,newlist}];
];


FindMid[x_,y_]:=Module[{x1=1,y1=0},
    NestWhile[(x1=IsolatingInterval[x,#][[2]];y1=IsolatingInterval[y,#][[1]];#/10)&,1,x1>=y1&]; 
    (* x1=IsolatingInterval[x,(y-x)/2][[2]];y1=IsolatingInterval[y,(y-x)/2][[1]]; *)
    Return[(y1+x1)/2];
]


FindMid[conflictstatelist_List]:=Module[{len=0,mid=Infinity,x},
    len=Length[conflictstatelist];
    If[len==0,Return[1]];
    If[conflictstatelist[[1,1]]!=-Infinity,
        (* Return[FindInstance[x < conflictstatelist[[1,1]] , {x}, Rationals][[1,1,2]]] *)
        x=IsolatingInterval[conflictstatelist[[1,1]]];
        Return[If[x[[1]]<x[[2]],x[[1]],x[[1]]-1/10]];
    ];
    If[conflictstatelist[[-1,2]]!=Infinity,
        (* Return[FindInstance[x > conflictstatelist[[-1,2]] , {x}, Rationals][[1,1,2]]] *)
       x=IsolatingInterval[conflictstatelist[[-1,2]]];
        Return[If[x[[1]]>x[[2]],x[[2]],x[[2]]+1/10]];
    ];
    Scan[If[conflictstatelist[[#-1,2]]<conflictstatelist[[#,1]],
            mid=FindMid[conflictstatelist[[#-1,2]],conflictstatelist[[#,1]]];
            (* mid=FindInstance[x> conflictstatelist[[#-1,2]] && x < conflictstatelist[[#,1]] , 
                 {x}, Rationals][[1,1,2]]; *)
            Return[],
            If[mid==Infinity && conflictstatelist[[#-1,2]]==conflictstatelist[[#,1]] && 
                !conflictstatelist[[#-1,3]] && !conflictstatelist[[#,3]],
                mid=conflictstatelist[[#-1,2]]]]&,
     Range[2,len]];
    Return[mid];
]


NRASolver[Clause1_,F1_,X_]:=Module[{a,cc,i,j,xmap=<||>,fmap=<||>,F=F1,Flevel,Fnow,conflictstatelist,Ci,Cli,Clause=Clause1,Clearn={},
                                    varnum,Clausenum,assignment=Association[Map[#->0&,X]],lorder,z,lnum,ML,M,Morder,VC,
                                    Cstatus,Clstatus,levell,levelc,levelcl,level,tmplevel,tmpc,tmpcl,status,nowc,conflict,
                                    getFnow,getFlevel,getClause,checkconflict,Polynomialroot,getorder,addl,getF,
                                    samplecell,getsamplecell,nextsamplecell},
    lnum=Length[F];
    (*Symmetry Check*)
    Module[{x0=X[[1]],C={}},
    Scan[
        If[(F1/.{#->x0,x0->#})==F1,AppendTo[F,{1,#-x0}];++lnum;AppendTo[C,{-lnum}];x0=#]&
    ,X[[2;;]]];
    (*Print[F];Print[Clause]*)
    If[Length[C]>Length[X]/2,Print["Find Symmetry: ",Map[Sequence@@F[[Abs[#],2]]&,C]];Clause={Sequence@@C,Sequence@@Clause}]
    ];
    (**)
    varnum=Length[X];
    Clausenum=Length[Clause];
    
    Scan[(xmap[X[[#]]]=# )&,Range[varnum]];
    Scan[(fmap[F[[#]]]=# )&,Range[lnum]];
    getorder=Function[l,
        Switch[l[[1]],
            1,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            2,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            3,xmap[l[[4]]],
            4,xmap[l[[4]]],
            5,Length[l[[3]]]
        ]
    ];
    Ci=Table[{},varnum];
    Cli=Table[{},varnum];
    levell=Table[{},varnum];
    conflictstatelist=Table[{},varnum];
    (* lorder=Table[If[Length[F[[i]]]>1,xmap[F[[i,3]]],Max[Map[xmap[#]&,Variables[F[[i,1]]]]]],{i,1,lnum}]; *)
    lorder=Map[Max[Map[xmap[#]&,Variables[#[[2]]]]]&,F];
    Scan[AppendTo[Ci[[Max[Map[lorder[[Abs[#]]]&,Clause[[#]]]]]],#]&,Range[Clausenum]];
    Scan[AppendTo[levell[[lorder[[#]]]],#]&,Range[1,lnum]];
    Flevel=Table[0,lnum];
    Fnow=Table[0,lnum];VC={Table[{},lnum],Table[{},lnum]};
    Cstatus=Table[{0,0},Clausenum];Clstatus={};
    level=1;
    ML=Table[{},varnum];
    Morder=Table[0,lnum];M=Table[0,lnum];
    levelc=Table[{},varnum];levelcl=Table[{},varnum];
    conflictstatelist[[level]]={};
    (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
    Scan[(Flevel[[#]]=F[[#,2]]/.(X[[1]]->z))&,levell[[level]]];
    (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
    levelc[[level]]=Map[{Clause[[#]],#}&,Ci[[level]]];
    Scan[(VC[[1]][[#]]={};VC[[-1]][[#]]={})&,levell[[level]] ];
    For[i=1,i<=Length[levelc[[level]]],++i,
        Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
        Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
    ];
    Polynomialroot[F_,Index_]:=If[Index>CountRoots[F,z],Infinity,Root[F,Index]];
    getsamplecell=Function[{l,a},
        Module[{newl},
            If[Length[a]!=0,
                newl=getF[{5,l,a}];
                ,newl=Nothing];
            newl]];
    nextsamplecell=Function[{lst,a,x0},
        Module[{pc=GetSampleInterval[lst,a,x0],nextl,fg,fl},
            nextl={getsamplecell[pc[[2]],a[[;;-2]]]};
            Scan[(
                    fg=getF[{3,#[[2]]/.(x0->z),#[[3]],x0}];
                    fl=getF[{4,#[[2]]/.(x0->z),#[[3]],x0}];
                    Switch[#[[1]],
                        Greater,AppendTo[nextl,-fg],
                        Equal,AppendTo[nextl,fg];AppendTo[nextl,fl],
                        Less,AppendTo[nextl,-fl]]
                )&,pc[[1]]]; 
            nextl
        ]
    ];
    samplecell=Function[i,If[F[[i,1]]==5 && SameQ[F[[i,4]],False],
        Module[{newlist=If[Length[F[[i,2]]]==1,
                            Pmc[F[[i,2,1]],assignment,X[[lorder[[i]]+1]]],
                            Ps[F[[i,2]],F[[i,3]],X[[lorder[[i]]+1]]]],
                x0=X[[lorder[[i]]]]},
                F[[i,4]]=nextsamplecell[newlist,F[[i,3]],x0];
        ]]];

    getFnow=(Switch[F[[#,1]],
        1,(F[[#,2]]/.assignment)>0,
        2,(F[[#,2]]/.assignment)==0,
        3,assignment[[lorder[[#]]]]>Flevel[[#]],
        4,assignment[[lorder[[#]]]]<Flevel[[#]],
        5,If[assignment[[;;lorder[[#]]]]==F[[#,3]],
            False,
            samplecell[#];
            MemberQ[Map[
              (*  If[F[[Abs[#],1]]==5,
                    !Xor[Fnow[[Abs[#]]],#>0],
                    !Xor[getFnow[Abs[#]],#>0]]&*)
                    (!Xor[Fnow[[Abs[#]]],#>0])&
                    ,F[[#,4]]],True]]
    ])&;
    getFlevel=(Switch[F[[#,1]],
        1,F[[#,2]]/.(X[[level]]->z)/.assignment,
        2,F[[#,2]]/.(X[[level]]->z)/.assignment,
        3,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        4,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        _,False
    ])&;
    getClause=Function[{c,l},
        Select[
            Map[{Map[
                    If[lorder[[Abs[#]]]==level,#,
                        !Xor[Fnow[[Abs[#]]],#>0]]&
                ,c[[#]]]/.(False->Nothing),#}&,l],
            Not[MemberQ[#[[1]],True]]&]
    ];
    checkconflict=Function[{list,index},
        Switch[F[[Abs[index],1]],
            1,CheckConflictHalf[list,Flevel[[Abs[index]]],z,index,index>0,False],
            3,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index>0,False],
            4,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index<0,False]]
    ];
    getF=Function[l,
        Module[{ans=fmap[l]},
            If[SameQ[Head[ans],Missing],
                AppendTo[F,l];++lnum;ans=lnum;fmap[l]=lnum;
                If[l[[1]]==5,AppendTo[F[[ans]],False]];
                AppendTo[lorder,getorder[l]];
                AppendTo[levell[[lorder[[ans]]]],lnum];AppendTo[Flevel,0];
                AppendTo[Fnow,0];AppendTo[M,0];
                AppendTo[Morder,0];AppendTo[VC[[1]],{}];AppendTo[VC[[-1]],{}];
                Flevel[[ans]]=getFlevel[ans];
                If[level>lorder[[ans]],Fnow[[ans]]=getFnow[ans]];
            ];
            ans
        ]
    ];
    addl=Function[l,
        Module[{index=l[[1]]},
            M[[Abs[index]]]=Sign[index];AppendTo[ML[[level]],l];Morder[[Abs[index]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[index],Abs[index]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[index],Abs[index]]]];
        ]
    ];
    While[True,
        tmpc=MinimalBy[Select[Range[Length[levelc[[level]]]],Cstatus[[levelc[[level,#,2]],2]]==0&],Cstatus[[levelc[[level,#,2]],1]]&];
        tmpcl=MinimalBy[Select[Range[Length[levelcl[[level]]]],Clstatus[[levelcl[[level,#,2]],2]]==0&],Clstatus[[levelcl[[level,#,2]],1]]&];
        If[Length[tmpc]==0 && Length[tmpcl]==0,
            assignment[X[[level]]]=FindMid[conflictstatelist[[level]]];
            (* Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[Length[F[[#]]]>1,If[F[[#,2]]>0,Fnow[[#]]=assignment[X[[level]]]>Flevel[[#]],Fnow[[#]]=assignment[X[[level]]]<Flevel[[#]]],Fnow[[#]]=((F[[#,1]]/.assignment)>0)]]&,levell[[level]]]; *)
            Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[F[[#,1]]!=5,Fnow[[#]]=getFnow[#]]]&,levell[[level]]];
            Scan[If[M[[#]]==0 && F[[#,1]]==5,Fnow[[#]]=getFnow[#]]&,levell[[level]]];
            
            ++level;
            If[level>varnum,Return[{"Sat",assignment}]];
            conflictstatelist[[level]]={};
            Scan[(M[[#]]=0)&,levell[[level]]];ML[[level]]={};
            (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
            Scan[(Flevel[[#]]=getFlevel[#])&,levell[[level]]];
            (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ];
            levelcl[[level]]=Select[ Map[{Select[Clearn[[#]],lorder[[Abs[#]]]==level& ],#}&,Cli[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clearn[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
            levelc[[level]]=getClause[Clause,Ci[[level]]];
            levelcl[[level]]=getClause[Clearn,Cli[[level]]];
            Scan[(VC[[1]][[#]]={};VC[[-1]][[#]]={})&,levell[[level]] ];
            For[i=1,i<=Length[levelc[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
                Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
            ];
            For[i=1,i<=Length[levelcl[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], -levelcl[[level,i,2]] ]&,levelcl[[level,i,1]]];
                Clstatus[[levelcl[[level,i,2]]]]={Length[levelcl[[level,i,1]]],0}
            ];
        ,
            status=-1;
            If[Length[tmpc]>0,
                If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==0,status=0;nowc=tmpc[[1]],
                    If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==1,status=1;nowc=tmpc[[1]],status=2;nowc=tmpc[[1]]]]
            ];
            If[status!=0 && Length[tmpcl]>0,
                If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==0,status=0;nowc=-tmpcl[[1]],
                    If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==1 && status!=1,status=1;nowc=-tmpcl[[1]]];
                    If[status==-1,status=2;nowc=-tmpcl[[1]]]
                ]
            ];
            If[status==0,
                If[nowc>0,conflict=Clause[[levelc[[level,nowc,2]]]],conflict=Clearn[[levelcl[[level,-nowc,2]]]]];
                While[status==0,
                    For[a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],Length[a] != 0, 
                               a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],
                        conflict = Fold[ClauseResolve[#1, ML[[level,Morder[[Abs[#2]]],2]], #2] &, conflict, a];
                    ];
                    If[Length[conflict]==0,Return[{"Unsat"}]];
                    tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                    
                    If[tmplevel==level,
                        a=Select[conflict,(lorder[[Abs[#]]]==level && F[[Abs[#],1]]==5)&];
                        If[Length[a]!=0,
                            (* Scan[samplecell[#]&,a];
                            If[Length[a]==1 || level==1,
                                conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                #1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]]; 
                            ,
                                Module[{c=<||>},
                                    conflict=Select[conflict,(lorder[[Abs[#]]]!=level || F[[Abs[#],1]]!=5)&];
                                    Scan[If[SameQ[Head[c[F[[#,3]]]],Missing],c[F[[#,3]]]={#},AppendTo[c[F[[#,3]]],#]]&,a];
                                    c=List@@c;
                                    c=Map[nextsamplecell[DeleteDuplicates[Flatten[Map[(F[[F[[#,4,1]],2]])&,#]]],F[[#[[1]],3]],X[[level]]]&,c];
                                    conflict=DeleteDuplicates[Flatten[{conflict,c}]];
                                ];
                            ]; *)
                            conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                samplecell[#2];#1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]];
                            tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                            ,
                            AppendTo[Clearn,conflict];
                            AppendTo[Cli[[level]],Length[Clearn]];
                            Scan[AppendTo[VC[[Sign[#],Abs[#] ]],-Length[Clearn]]&, Select[conflict,lorder[[Abs[#]]]==level& ] ];
                            a=Select[conflict,lorder[[Abs[#]]]==level&];
                            AppendTo[levelcl[[level]],{a,Length[Clearn]}];
                            AppendTo[Clstatus,{Length[Select[a,M[[Abs[#]]]==0&]],0}];
                            If[Clstatus[[-1,1]]<2,status=1,status=2];
                            nowc=-Length[levelcl[[level]]];
                            If[Clstatus[[-1,1]]==0,
                                If[Length[a]==1,a=Max[Map[Morder[[Abs[#]]]&,a]]-1,
                                    a=RankedMax[Map[Morder[[Abs[#]]]&,a],2]];
                                Scan[
                                    (M[[Abs[#[[1]]]]]=0;
                                    Scan[If[#>0,--Cstatus[[#,2]];++Cstatus[[#,1]],--Clstatus[[-#,2]];++Clstatus[[-#,1]]]&,VC[[Sign[#[[1]]],Abs[#[[1]]]]]];
                                    Scan[If[#>0,++Cstatus[[#,1]],++Clstatus[[-#,1]]]&,VC[[-Sign[#[[1]]],Abs[#[[1]]]]]];)&
                                ,ML[[level,a+1;;]]];
                                ML[[level]]=ML[[level,;;a]];
                                (* conflictstatelist[[level]]=Fold[
                                    If[Length[F[[Abs[#2[[1]]]]]]==1,
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],X[[level]],#2[[1]],#2[[1]]>0,False][[2]],
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],#2[[1]],!Xor[F[[Abs[#2[[1]]],2]]>0,#2[[1]]>0],False][[2]]]&
                                ,{},ML[[level]]]]; *)
                                conflictstatelist[[level]]=Fold[checkconflict[#1,#2[[1]]][[2]]&,{},ML[[level]]]]]];
                    level=tmplevel;
                ]
            ];
            If[nowc>0,cc=levelc[[level,nowc,1]],cc=levelcl[[level,-nowc,1]]];
            If[status==1,
                a=Select[cc,M[[Abs[#]]]==0&][[1]];
            ,
                a=MaximalBy[Select[cc,M[[Abs[#]]]==0&],Length[Select[VC[[Sign[#],Abs[#]]],If[#<0,Clstatus[[-#,2]]==0,Cstatus[[#,2]]==0]&]]&][[1]];
            ];
            (* If[Length[F[[Abs[a]]]]==1,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],X[[level]],a,a>0,False];
            ,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],a,!Xor[F[[Abs[a],2]]>0,a>0],False];
            ]; *)
            tmpc=checkconflict[conflictstatelist[[level]],a];
            If[tmpc[[1]],
                conflictstatelist[[level]]=tmpc[[2]];
                If[nowc>0,cc=Clause[[levelc[[level,nowc,2]]]],cc=Clearn[[levelcl[[level,-nowc,2]]]]];
            ,
                cc=DeleteDuplicates[Map[#[[4]]&,tmpc[[2]]]];
                If[level>1,
                    Module[{l},
                        l=Map[Function[x,
                                If[F[[Abs[x],1]]==1 || F[[Abs[x],1]]==2,
                                    F[[Abs[x],2]],
                                    F[[Abs[x],2]]/.(z->X[[level]])]]
                            ,cc];
                        l=Select[DeleteDuplicates[Flatten[Map[FactorList,l][[All,All,1]]]],UnsameQ[Variables[#],{}]&];
                        conflict=getsamplecell[{l},assignment[[;;level-1]]];
                    ]
                    ,
                    conflict=Nothing;
                ];
                (* cc=Flatten[{conflict,Map[Minus,cc]}];  *)
                cc={Sequence@@Map[Minus,cc],conflict};
                a=-a;
                status=1;
            ];
            If[status==1,addl[{a,cc}],addl[{a}]];
            (* M[[Abs[a]]]=Sign[a];
            If[status==1,AppendTo[ML[[level]],{a,cc}],AppendTo[ML[[level]],{a}]];
            Morder[[Abs[a]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            (* Theoretical reasoning *)
            (* If[Length[F[[Abs[a]]]]>1 && UnsameQ[Head[status=fmap[{F[[Abs[a],1]],-F[[Abs[a],2]],F[[Abs[a],3]]}]],Missing] && M[[status]]==0 , *)
            If[F[[Abs[a],1]]==3 || F[[Abs[a],1]]==4,
                status=getF[{7-F[[Abs[a],1]],Sequence@@F[[Abs[a],2;;]]}];
                If[M[[status]]==0,cc=a;a=-1*Sign[a]*status;cc={a,-cc};addl[{a,cc}];]
                (* M[[Abs[a]]]=Sign[a];AppendTo[ML[[level]],{a,cc}];Morder[[Abs[a]]]=Length[ML[[level]]];
                Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
                Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            ]
        ]

    ]
];


End[];


EndPackage[];
