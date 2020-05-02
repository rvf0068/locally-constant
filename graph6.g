#FIXME: make private methods not globally accesible?

AsciiList:="\000\001\002\003\004\005\006\007\010\011\012\013\014\015\016\017\020\021\022\023\024\025\026\027\030\031\032\033\034\035\036\037\040\041\042\043\044\045\046\047\050\051\052\053\054\055\056\057\060\061\062\063\064\065\066\067\070\071\072\073\074\075\076\077\100\101\102\103\104\105\106\107\110\111\112\113\114\115\116\117\120\121\122\123\124\125\126\127\130\131\132\133\134\135\136\137\140\141\142\143\144\145\146\147\150\151\152\153\154\155\156\157\160\161\162\163\164\165\166\167\170\171\172\173\174\175\176\177\200\201\202\203\204\205\206\207\210\211\212\213\214\215\216\217\220\221\222\223\224\225\226\227\230\231\232\233\234\235\236\237\240\241\242\243\244\245\246\247\250\251\252\253\254\255\256\257\260\261\262\263\264\265\266\267\270\271\272\273\274\275\276\277\300\301\302\303\304\305\306\307\310\311\312\313\314\315\316\317\320\321\322\323\324\325\326\327\330\331\332\333\334\335\336\337\340\341\342\343\344\345\346\347\350\351\352\353\354\355\356\357\360\361\362\363\364\365\366\367\370\371\372\373\374\375\376\377";

  #FIXME: error management, data types.
AsciiToChar:=function(num) return AsciiList[num+1]; end; 
  #FIXME: error management, data types.
CharToAscii:=function(char) return Position(AsciiList,char)-1; end; 

NumToBinList:=function(n)
   local NumBin,d0;
   if not (IsInt(n) and n>=0) then 
     Error("Usage: n must be a non-negative integer \
in function NumToBinList(n)\n");
   fi;
   if n=0 then return [0]; fi;
   if n=1 then return [1]; fi;
   d0:=(n mod 2);
   NumBin:=NumToBinList((n-d0)/2);
   Add(NumBin,d0);
   return NumBin;
end;

BinListToNum:=function(L)
  #FIXME: error management, data types.
  local num,b;
  num:=0;
  for b in L do 
    num:=num*2+b;
  od;
  return num;
end;

PadLeftnSplitList6:=function(L) 
  #FIXME: error management, data types.
   local n,n6,L1,LL,i;
   n:=Length(L);
   n6:=Maximum(1,Int((n+5)/6)*6);
   L1:=Concatenation(List([n+1..n6],z->0),L);
   LL:=[];
   for i in [1..n6/6] do 
     LL[i]:=L1{[6*i-5..6*i]};
   od;
   return LL;
end;

PadRightnSplitList6:=function(L) 
  #FIXME: error management, data types.
   local n,n6,L1,LL,i;
   n:=Length(L);
   n6:=Maximum(1,Int((n+5)/6)*6);
   L1:=Concatenation(L,List([n+1..n6],z->0));
   LL:=[];
   for i in [1..n6/6] do 
     LL[i]:=L1{[6*i-5..6*i]};
   od;
   return LL;
end;

BinListToNumList:=function(L) 
  #FIXME: error management, data types.
    local Ln;
    Ln:=PadRightnSplitList6(L);
    Ln:=List(Ln,l->BinListToNum(l)+63);
    return Ln;
end;

NumListToString:=function(L) 
  #FIXME: error management, data types.
   local str,n;
   str:=[];
   for n in L do
     Add(str,AsciiToChar(n)); 
   od;
   return str;
end;

McKayR:=function(L) 
  #FIXME: error management, data types.
    return NumListToString(BinListToNumList(L));
end;

McKayN:=function(n) 
  #FIXME: error management, data types.
   local str,str2;
   str:=[];str2:=NumToBinList(n);
   if(n<0 or n>68719476735) then return fail; fi;
   if n<=62 then
      str2:=Concatenation(List([Length(str2)+1..6],z->0),str2); 
   elif n<=258047 then 
       Add(str,AsciiToChar(126));
       str2:=Concatenation(List([Length(str2)+1..18],z->0),str2); 
   else 
       Add(str,AsciiToChar(126)); 
       Add(str,AsciiToChar(126)); 
       str2:=Concatenation(List([Length(str2)+1..36],z->0),str2);
   fi;
   str2:=McKayR(str2);
   return Concatenation(str,str2); 
end;

StringToBinList:=function(Str) 
    local car,L,num,aux;
    L:=[];
    for car in Str do
       num:=CharToAscii(car)-63;
       aux:=NumToBinList(num);
       aux:=Concatenation(List([Length(aux)+1..6],z->0),aux);
       Append(L,aux); 
    od;
    return L;
end;

###################################

# Graph6ToGraph:=function(Str)
#    local pos,n,bv,i,j,k,M;
#    if Str[Length(Str)] in "\n\r" then Remove(Str); fi;  
#    if Str[Length(Str)] in "\n\r" then Remove(Str); fi;  
#    if Str{[1,2]}="~~" then
#       pos:=9;
#       n:=BinListToNum(StringToBinList(Str{[3..8]}));
#    elif Str[1]='~' then
#       pos:=5;
#       n:=BinListToNum(StringToBinList(Str{[2..4]}));
#    else
#       pos:=2;
#       n:=BinListToNum(StringToBinList(Str{[1]}));
#    fi;
#    bv:=StringToBinList(Str{[pos..Length(Str)]}); #bv:=bitvector;
#    M:=List([1..n],z->List([1..n],w->false));
#    k:=0;
#    for j in [1..n] do 
#      for i in [1..j-1] do
#        k:=k+1;
#        if bv[k]=1 then M[i][j]:=true; fi;
#      od;
#    od;
#    return GraphByAdjMatrix(M:GraphCategory:=SimpleGraphs);
# end;

# GraphToGraph6:=function(G)    
#    #FIXME: Incomplete
# end;

# ImportGraph6:=function(filename) 
#    local inp,str,L; 
#    L:=[];
#    inp:=InputTextFile( filename );
#    if inp=fail then
#       Print("#W Unreadable File\n"); 
#       return fail; 
#    fi;
#    str:=ReadLine(inp);
#    while(str<>fail) do 
#       Add(L,Graph6ToGraph(str));
#       str:=ReadLine(inp);
#    od;
#    CloseStream(inp);
#    return L;
# end;

# ExportGraph6:=function(L) 
#    ###some useful code:
#    #FIXME: Incomplete
#    #PrintTo(filename,Order(G),"\n");
#    #AppendTo(filename,coord[i][1], " ");
# end;



