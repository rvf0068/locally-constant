RequirePackage("yags");
Read("McKayToHarary.g");
Read("graph6.g");
Read("simplex.g");
Read("LocL.g");

Lh:=[TrivialGraph];
Append(Lh,ImportGraph6("AllGraphs/graph2.g6"));
Append(Lh,ImportGraph6("AllGraphs/graph3.g6"));
Append(Lh,ImportGraph6("AllGraphs/graph4.g6"));
Append(Lh,ImportGraph6("AllGraphs/graph5.g6"));
Append(Lh,ImportGraph6("AllGraphs/graph6.g6"));
Append(Lh,ImportGraph6("AllGraphs/graph7.g6"));
#Append(Lh,ImportGraph6("AllGraphs/graph8.g6"));
#Append(Lh,ImportGraph6("AllGraphs/graph9.g6"));

te:=List([1..208],function(x) if McKayToHarary(x) in TienenExtension then return 1; else return 0;fi; end);
Lr:=List([1..Length(Lh)],x->3);
Lt:=List([1..Length(Lh)],x->infinity);

except:=[55,60,61,89,91,92];

Read("GenLoc.g");

#ProfileFunctions([Inclusions, Reinclusions, PropertyMorphism, MonoMorphism,PropertyMorphisms, NextPropertyMorphism,IsIso,IsIsomorphicGraph, AutomorphismGroup, IsPartialExtension, ChooseWisely, RepModAut, SuperGraph, ExtensionAtXwFG, ExtensionsAtXwF, ExtensionsAtX, GenLoc]);

DoAll:=function() 
    local n,t1,t2,r;
    for n in [1..Length(Lh)] do 
       PrintTo(AuxInfo1,"n:=",n,"\n");
       if Lr[n] <=1 then continue; fi; # ya se calculó previamente.
       if n in except then Lr[n]:=2; continue; fi; #lo omitimos deliberadamente
       t1:=TimeInSeconds();
          r:=GenLoc(Lh[n]);
       t2:=TimeInSeconds();
       if r=3 then 
          Lr[n]:=3; #faltó tiempo
       elif r=fail then
          Lr[n]:=0;Lt[n]:=t2-t1; # L no tiene extensión.
       else 
          Lr[n]:=1;Lt[n]:=t2-t1; # L sí tiene extensión.
       fi;
    od;
end;



