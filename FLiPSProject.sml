(*PROGETTO FLiPS : ESERCIZIO 2 *)


load "Listsort";
load "Int";
load "Bool";
load "Random";



(*Mi viene restituito 0 o 1 da random_number r => utile per l'implementazione della composizione paralella*)
val r = Random.newgen();
val random_number = Random.range(0,2)

datatype type_L =  int  
				| unit  
				| bool 
				| Func of type_L * type_L 
				| proc


datatype oper = piu 
			   | mu 
			   | eq

type loc = string
datatype type_loc = intref
type typeE = (loc * type_loc) list

(************************* SYNTAX  *****************************)
datatype exp =
        Boolean of bool
    |   Integer of int
    |   Op of exp * oper * exp
    |   If of exp * exp * exp
    |   Assign of loc * exp
    |   Skip 
    |   Seq of exp * exp 				(* e1;e2                *)
    |   While of exp * exp
    |   Deref of loc 
	|	Var of int						(* Var(x)           Ok  *)
	|	Fn of type_L * exp  			(* Fn (t, e)        Ok  *)
	|	App of exp * exp	  			(* App(e1,e2)       Ok  *)
	|   App_CBN of exp * exp 			(* App_CBN(e1, e2)        *)
	|	Let of type_L * exp * exp		(* Let(t, e1, e2)   Ok  *)
	|	Fix of exp						(* Fix(e)  		    Ok    *)
	| 	Fix_CBN of exp					(* Fix_CBN(e)                     *)
	|	Fib_ric of exp 					(* Fib_ric(n)       Ok       *)
	|	Parallel of exp * exp 			(* Parallel (e1, e2)     Ok      *)
	|	Await of exp * exp				(* Await (e1, e2)   .. ??   *)
	|	RepPar of exp
	|	AwtPar of exp 					
	
	
	
(*Considerando che le funzioni sono terminali, mi definisco una funzione che mi controlla se una determinata espressione data in input è un terminale*)
fun  valore (Integer n) = true
  |  valore (Boolean b) = true
  |  valore (Skip)      = true
  |  valore (Fn(t,e))   = true
  |  valore _           = false


type store = (loc * int) list

(*e1 -> e2*)
(*(exp * store) -> (exp * store) option*)
(*(''a * b) list *''a -> b option*)

(*Mi definisco una funzione che mi permette di accedere al contenuto di una locazione nello store*)
(*Lo store + una lista di coppie (loc*int*)
fun lookup ( [], l ) = NONE
  | lookup ( (l',n')::pairs, l) = 
    if l=l' then SOME n' else lookup (pairs,l)


(* Funzione di supporto per definire Var.
Se si parte da una lista vuota, non si fa niente. se invece m = 0, viene restituito il primo 
elemento della lista. altrimenti, viene richiamata partendo dal secondo elemento*)

fun select [] m = NONE						
  | select (hd::tl) m = if m = 0 then
                     SOME hd
                    else 
                      select tl (m - 1)
					  

(* fn:store * (loc*int)->store option *)

(* fn: (''a * 'b) list -> (''a * 'b) list -> ''a * 'b -> (''a * 'b) list option *)
(*Front è una lista inizialmente vuota che viene riempita scorrendo lo store.
Se viene trovata una locazione da modificare viene ritornata una nuova lista fatta 
dagli elementi di front a cui viene concatenata la parte rimanente dello store che viene associata
alla locazione richiesta dal nuovo valore*)
fun update'  front [] (l,n) = NONE
 |  update'  front ((l',n')::pairs) (l,n) = 
    if l=l' then 
        SOME(front @ ((l,n)::pairs) )
    else 
        update' ((l',n')::front) pairs (l,n)

fun update (s, (l,n)) = update' [] s (l,n)


(*Viene sostituita l'espressione "e" al posto della prima variabile LIBERA(non bound) di indice n all'interno dell'espressione
passata come terzo parametro*)
fun   subst e n (Integer n')           = Integer n'
	| subst e n (Boolean b)            = Boolean b
	| subst e n (Op (e1, opr, e2))     = Op (subst e n e1, opr, subst e n e2)
	| subst e n (If (e1, e2, e3))      = If (subst e n e1, subst e n e2, subst e n e3)
	| subst e n (Assign (l,e1))        = Assign(l, subst e n e1)
	| subst e n (Deref l)              = Deref l
	| subst e n (Skip)             	   = Skip
	| subst e n (Seq (e1, e2))         = Seq (subst e n e1, subst e n e2)
	| subst e n (While(e1, e2))        = While(subst e n e1, subst e n e2)
	| subst e n (Var n1)               = if n=n1 then e else Var n1
	| subst e n (Fn (t, e1))           = Fn (t, subst e (n+1) e1) 
	| subst e n (App (e1, e2))         = App (subst e n e1,subst e n e2)
	| subst e n (Let (t, e1, e2))      = Let (t,subst e n e1,subst e (n+1) e2)
	| subst e n (Fix(e1))              = Fix(subst e n e1)
	| subst e n (Parallel(e1, e2))     = Parallel(subst e n e1, subst e n e2)
	| subst e n (Await(e1, e2))        = Await(subst e n e1, subst e n e2)
	| subst e n (RepPar(e1))           = RepPar(subst e n e1)
	| subst e n (AwtPar(e1))           = AwtPar(subst e n e1)
  


(************************************** SMALL STEP SEMANTICS *****************************************)

fun red (Integer n,s) = NONE
	| red (Boolean b,s) = NONE
	| red (Op (e1,opr,e2),s) = 
    (case (e1,opr,e2) of
         (Integer x1, piu, Integer x2) => SOME(Integer (x1+x2), s)   				(*op+*)
       | (Integer x1, mu, Integer x2) => SOME(Boolean (x1 >= x2), s)				(*op>=*)
	   | (Integer x1, eq, Integer x2) => SOME(Boolean(x1=x2),s) 					(*op =*)
       | (e1,opr,e2) => (                                               
         if (valore e1) then (                                        
             case red (e2,s) of 
                 SOME (e2',s') => SOME (Op(e1,opr,e2'),s')     						(*op2*)
               | NONE => NONE )                           
         else (                                                 
             case red (e1,s) of 
                 SOME (e1',s') => SOME(Op(e1',opr,e2),s')      						(*op1*)
               | NONE => NONE ) ) )
	| red (If (e1,e2,e3),s) =
     (case e1 of
         Boolean(true) => SOME(e2,s)                           
       | Boolean(false) => SOME(e3,s)                          
       | _ => (case red (e1,s) of
                   SOME(e1',s') => SOME(If(e1',e2,e3),s')     						(*if*)
                 | NONE => NONE ))
	| red (Deref l,s) = 
    (case lookup  (s,l) of                
          SOME n => SOME(Integer n,s)                          
        | NONE => NONE )                  
	| red (Assign (l,e),s) =
    (case e of                                                 
         Integer n => (case update (s,(l,n)) of 
                           SOME s' => SOME(Skip, s')  								(*Assign 1*)          
                         | NONE => NONE)                                   
       | _ => (case red (e,s) of                           
                   SOME (e',s') => SOME(Assign (l,e'), s')    
                 | NONE => NONE  ) )                          
	| red (While (e1,e2),s) = SOME( If(e1,Seq(e2,While(e1,e2)),Skip),s) 			(* (while) *)
	| red (Skip,s) = NONE                                     
	| red (Seq (e1,e2),s) =                                   
    (case e1 of                                                 
        Skip => SOME(e2,s)    														(*Seq 1*)                                  
      | _ => ( case red (e1,s) of                           
                 SOME (e1',s') => SOME(Seq (e1',e2), s')       
               | NONE => NONE ) ) 

	
  (* subst e 0 e' sostituisce e per la variabile più esterna libera in e' partendo dall'indice 0 *)
  (*************************************************** SEMANTICA VAR, FN, APP ***************************************************************)

	|red(Var (e), s) = NONE
	| red(Fn(t, e), s) = NONE
	| red(App(e1, e2), s) =
	(
		case e1 of
		  Fn(t,e) =>																(* Se e1 è una funzione*)
			(if (valore e2) then 
				SOME(subst e2 0 e,s)     											(* CBV-Fn, se e2 è un valore, viene fatta la sostituzione di tutte le occorenze libere di x nella funzione*)
				
			else(
				case red(e2,s) of
					SOME (e2',s') => SOME(App(e1,e2'),s')   						(* CBV-App2, e2 non è un valore, quindi può fare un passo, viene valutato*)
				| NONE => NONE
			)
			)
		
		
	    |_=> (case red(e1,s) of
				SOME(e1',s') => SOME(App(e1',e2),s')								(* CBV-App1 In tutti gli altri casi, in particolare,quando è necessario valutare e1 cioè se e1 può fare un passo*)
				| NONE => NONE
			)
		
	)
	
	|red(App_CBN(e1, e2), s) = 
		(
			case e1 of 
				Fn(t, e) => SOME(subst e 0 e2, s)									(* CBN-Fn , se e1 è una funzione*)
			|_ => (case red(e1, s) of
				SOME(e1', s') => SOME(App_CBN(e1', e2), s')							(* CBN-App, se e1 è riducibile *)
				| NONE => NONE)
		)
	
	
	(*************************************************** SEMANTICA LET ***************************************************************)

	
	| red(Let(t,e1,e2),s) = 
		(	if (valore e1) then 
				SOME (subst e1 0 e2,s)												(* CBV-Let2 se e1 è un valore, sostituisco in e2 le occorenze di e1 con il valore*)
			else(
				case red(e1,s) of
					SOME(e1',s') => SOME(Let(t,e1',e2),s')							(* CBV-Let1 e1 non è un valore, fa un passo e va nello stato e1' store s' *)
				| NONE => NONE
			)
		
		)
	
	
	(*************************************************** SEMANTICA FIX ***************************************************************)

	| red(Fix(e),s) = 										
		(case e of
			Fn(Func(t1,t2),e2) =>									
				SOME(App(e,Fn(t1,App(Fix(e),Var 0 ))),s )							(* Fix-CBV *)
	            |_ => NONE	
            |_ => NONE				
		)
		
	| red(Fix_CBN(e), s) = SOME(App_CBN(e,Fix_CBN(e)),s)							(* Fix-CBN *)

	(*************************************************** FIBONACCI ***************************************************************)
	
    (*Simile all'esempio del fattoriale visto a lezione => 
	fib = fn f.fn z.if z= 0 then 1 else if z = 1 then 1 else f(z-1)+f(z-2)
	Fib_ric = fix(fib)*)
	| red(Fib_ric(e), s) = 
        (
            (* ridefinisco internamente evaluate*)
            let fun evaluate(e1, s1) = case red(e1,s1) of 
										SOME(e',s') => evaluate(e',s')
										|NONE => SOME(e1, s1)
            in 
              evaluate(App(Fix(
                Fn(Func(int, int), 
                Fn(int, If(Op(Var 0, eq, Integer 0), Integer 0, 
                If(Op(Var 0, eq, Integer 1), Integer 1, 
                Op(App(Var 1, Op(Var 0, piu, Integer ~1)), piu,  App(Var 1, Op(Var 0, piu, Integer ~2)))))))), e), s)
            end                        
        )
	
	(*************************************************** SEMANTICA PARALLELA ***************************************************************)

	
	(*Usando la struttura random, faccio una estrazione casuale (come un lancio di moneta)*)
	
	| red(Parallel(e1, e2), s) = (
		if(random_number r = 0) 
		then(
			case e1 of
				skip => SOME(e2,s)												(* (end_L)  Se e1 è un processo terminale, lo termino e vado con l'esecuzione di e2*)
				|_ => (case red(e1,s) of 				  						(*  Se inizio con e1 e può fare un passo *)
					SOME(e1',s') => SOME(Parallel(e1',e2),s')  					(* (par_L) lo fa, va nello stato e1' store s'*)
					| _=> NONE
					)			
		)else(																	(* Se invece inizio con e2*)
			case e2 of
				skip => SOME(e1,s)												(*(end-R) Se è un processo terminale, vado a valutare e1*)
				|_ => (case red(e2,s) of										(* Se inizio con e2 e può fare un passo ovvero non è un processo terminale*)
					SOME(e2',s') => SOME(Parallel(e1,e2'),s')					(* (par-R)Fa il passo e va nello stato e2', store s'*)
					| _=> NONE
					)
		)
	)
	
	(*************************************************** SEMANTICA AWAIT ***************************************************************)

	
	(*Quando la guardia e1 è vera (valuta a vero), e2 può essere eseguita in maniera atomica in un solo passo.. mi serve definire internamente la big step semantics*)
	| red (Await (e1,e2), s) =  (
		let 
			fun evaluate (e,s) = case red (e,s) of 
								NONE => (e,s)
								| SOME (e',s') => evaluate (e',s')
		in
			case evaluate (e1,s) of 
				(Boolean true, s') => 
					(case evaluate(e2,s') of 
						(Skip,s'') => SOME(Skip,s'')							(*Viene eseguito e2 in un solo passo*)
						|_ => NONE
					)
				|(Boolean false, s') => NONE									(*Se e1 valuta a false, non si entra nell'Await*)
				|_=> case red(e1,s) of											(*Se e1 non è un booleano ed è riducibile, viene ridotto e richiamato l'Await*)
					SOME(e1',s') => SOME(Await(e1',e2),s')
					| NONE => NONE
		end			
	
	)
	
	
	(*************************************************** SEMANTICA RepPar ***************************************************************)
	| red(RepPar(e), s) = 
	(
		let 
			val rP = Fn(Func(unit, unit), Fn(unit, Parallel(Var 0, App_CBN(Var 1, Var 0)))) 						(* (RepPar) var 0 -> x, var 1 -> f*)
		in
			SOME(App_CBN(Fix_CBN(rP),e), s)
		end
		
	)
	(*************************************************** SEMANTICA AwPar ***************************************************************)
	| red(AwtPar(e),s) =
	(
		let 
			val aP = Fn(Func(unit, unit), Fn(unit, Parallel(Await(Boolean true, Var 0 ), App_CBN(Var 1, Var 0))))  	(* (AwtPar) var 0 -> x, var 1 -> f*)
		in
			SOME(App_CBN(Fix_CBN(aP), e), s)
		end
	)
	
	


(* Semantica big-step: expr * store => (expr store) option *)

fun evaluate (e,s) = case red (e,s) of 
                         NONE => (e,s)
                       | SOME (e',s') => evaluate (e',s')


(*   e,s -> e2,s2 ---..... *)





fun infertype gamma (Integer n) = SOME int

  | infertype gamma (Boolean b) = SOME bool
  
  | infertype gamma (Op (e1,opr,e2)) 
    = (case (infertype gamma e1, opr, infertype gamma e2) of
          (SOME int, piu, SOME int) => SOME int					(*Regola : Op+ *)
        | (SOME int, mu, SOME int) => SOME bool					(*Regola : Op mu*)
        | _ => NONE)
	
  (*Regola If : e1 è di tipo bool. Per e2, e3 si definiscono 2 tipi, e si verifica che siano uguali*)	
  | infertype gamma (If (e1,e2,e3)) 			
    = (case (infertype gamma e1, infertype gamma e2, infertype gamma e3) of
           (SOME bool, SOME t2, SOME t3) => 
           (if t2=t3 then SOME t2 else NONE)
         | _ => NONE)
	
  | infertype gamma (Deref l) 									(*Regola : Deref*)
    = (case lookup ((#1 gamma),l) of
           SOME intref => SOME int
         | NONE => NONE)
		 
  | infertype gamma (Assign (l,e)) 								(*Regola: Assign*)
    = (case (lookup ((#1 gamma),l), infertype gamma e) of
           (SOME intref,SOME int) => SOME unit
         | _ => NONE)
		 
  | infertype gamma (Skip) = SOME unit
  
  | infertype gamma (Seq (e1,e2))  								(*Regola: Seq*)
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME unit, SOME t2) => SOME t2
         | _ => NONE )
		 
  | infertype gamma (While (e1,e2)) 							(*Regola: While*)
    = (case (infertype gamma e1, infertype gamma e2) of
           (SOME bool, SOME unit) => SOME unit 
         | _ => NONE )
		 
   				
  | infertype gamma (Var n) = select (#2 gamma) n				(*Regola: Var*)
  
  | infertype gamma(Fn(t, e)) 
	= ( case (infertype (#1 gamma, t::(#2 gamma)) e) of			(*Regola : Fn*)
		(SOME t') => SOME(Func(t, t'))
		| NONE => NONE )
		
  | infertype gamma(App(e1, e2))								(*Regola: App*)
	= (case (infertype gamma e1, infertype gamma e2) of 
		(SOME(Func(t1,t2)), SOME t3) => (if t1 = t3 then SOME t2 else NONE)
		|_=> NONE)
	
  (*App_CBN definita solo per la RepPar e AwtPar*)
  | infertype gamma(App_CBN(e1, e2))							(*Regola: App_CBN*)
	= (case (infertype gamma e1, infertype gamma e2) of 
		(SOME(Func(t1,t2)), SOME t3) => (if t1 = t3 then SOME t2 else NONE)
		|_=> NONE)
	
  | infertype gamma (Let(t, e1, e2))							(*Regola: Let*)
	= (case (infertype gamma e1, infertype (#1 gamma, t::(#2 gamma)) e2) of
		(SOME t1, SOME t2) => if t1 = t then SOME t2 else NONE
	   |_ => NONE)

  | infertype gamma (Fix(e))									(*Regola T-Fix*)
	= (case (infertype gamma e) of
		(SOME(Func((Func(t1, t2), Func(t3, t4))))) => if (t1=t3 andalso t2=t4) then SOME(Func(t1,t2)) else NONE
		|_=> NONE)
	
  (*Fix_CBN definita solo per la RepPar e AwtPar*)	
  | infertype gamma (Fix_CBN(e))								(*Regola: Fix-CBN*)
	= (case (infertype gamma e) of
		(SOME(Func((Func(t1, t2), Func(t3, t4))))) => if (t1=t3 andalso t2=t4) then SOME(Func(t1,t2)) else NONE
		|_=> NONE)
		
  | infertype gamma (Fib_ric(e)) = 								(*Regola Fib_ric*)
    (
      case(infertype gamma e) of
        (SOME int) => SOME int
        | _ => NONE

    )
		
  | infertype gamma (Parallel(e1, e2)) 							(*Regola: T-par*)
	= (case (infertype gamma e1, infertype gamma e2) of
		 (SOME (unit), SOME (unit)) => SOME (proc)
		|(SOME (unit), SOME (proc)) => SOME (proc)
		|(SOME (proc), SOME (unit)) => SOME (proc)
		|(SOME (proc), SOME (proc)) => SOME (proc)
		|_=> NONE)

  | infertype gamma (Await(e1, e2))								(*Regola: Await*)
	= (case (infertype gamma e1, infertype gamma e2) of
		(SOME Bool, SOME unit ) => SOME (unit)
		|_=> NONE)
	
   (*"e" viene data in input a Fix(P). Sapendo che P ha tipo (unit -> unit) -> (unit -> unit), Fix(P) avrà tipo (unit -> unit)
   quindi e dovrà esser necessariamente di tipo unit*)
  | infertype gamma (RepPar(e))
	= (case (infertype gamma e) of
		(SOME unit) => SOME proc
		|_ => NONE)

  (* Similmente, sapendo che l'espressione "e" viene data in input a Fix(A) il suo tipo deve 
          essere necessariamente unit. *)	
  | infertype gamma (AwtPar(e)) = 
    (
      case(infertype gamma e) of 
        (SOME unit) => SOME proc
        | _ => NONE      
    );
 
(*1+2
e1 ; ife1then
load "Int"
load "Listsort"  *) 
		 
fun   printop piu = "+"
	| printop mu = ">="
	| printop eq = "="
	
fun   printtype int  =  "int"
	| printtype bool = "bool"
	| printtype unit = "unit"
	| printtype proc = "proc" 
	| printtype (Func(t1, t2)) = "(" ^ (printtype t1) ^ "->" ^ (printtype t2) ^ ")"
                         
fun   printexp (Integer n) = Int.toString n
	| printexp (Boolean b) = Bool.toString b
	| printexp (Op (e1,opr,e2)) 
		= "(" ^ (printexp e1) ^ (printop opr) 
		^ (printexp e2) ^ ")"
	| printexp (If (e1,e2,e3)) 
		= "if " ^ (printexp e1 ) ^ " then " ^ (printexp e2)
		^ " else " ^ (printexp e3)
	| printexp (Assign (l,e))       =  l ^ ":=" ^ (printexp e )
    | printexp (Skip) = "skip"
    | printexp (Seq (e1,e2))        =  (printexp e1 ) ^ ";" ^ (printexp e2)
    | printexp (While (e1,e2))      =  "while " ^ (printexp e1 ) ^ " do " ^ (printexp e2)						   
    | printexp (Deref l)			=  " !" ^ l
	| printexp (Var n) 			    =  " var_ " ^ Int.toString n
	| printexp (Fn(t,e)) 			=  " fn : " ^ (printtype t) ^ "=>" ^ (printexp e)
	| printexp (App(e1,e2))         =  "(" ^ (printexp e1) ^ " " ^ (printexp e2) ^ ")"
	| printexp (App(e1, e2))        =  "(" ^ (printexp e1) ^ " " ^ (printexp e2) ^ ")"
	| printexp (App_CBN(e1, e2))    =  "(" ^ (printexp e1) ^ " " ^ (printexp e2) ^ ")"
	| printexp (Let(t, e1, e2))     =  " Let x " ^ ":" ^ (printtype t)^ "=" ^ (printexp e1) ^ "in" ^ (printexp e2)
	| printexp (Fix(e))             =  " Fix " ^  "(" ^ (printexp e) ^")"
	| printexp (Fix_CBN(e))         =  " Fix " ^  "(" ^ (printexp e) ^")"
	| printexp (Fib_ric(e))         =  " Fibonacci " ^ "(" ^ (printexp e) ^ ")"
	| printexp (Parallel(e1, e2))   =  " (" ^ (printexp e1) ^ "||" ^ (printexp e2) ^ ")"
	| printexp (Await(e1, e2))      =  " Await " ^ (printexp e1) ^ " protect " ^ (printexp e2) ^ " end; "
	| printexp (RepPar(e))          =  " RepPar " ^ "(" ^ (printexp e) ^ ")"
	| printexp (AwtPar(e))          =  " AwtPar " ^ "(" ^ (printexp e) ^ ")"


fun printstore' [] = ""
  | printstore' ((l,n)::pairs) = l ^ "=" ^ (Int.toString n) 
                                   ^ " " ^ (printstore' pairs)

fun printstore pairs = 
    let val pairs' = Listsort.sort 
                         (fn ((l,n),(l',n')) => String.compare (l,l'))
                         pairs
    in
        "{" ^ printstore' pairs' ^ "}" end


fun printconf (e,s) = "< " ^ (printexp e) 
                             ^ " , " ^ (printstore s) ^ " >"


fun printred' (e,s) = 
    case red (e,s) of 
        SOME (e',s') => 
        ( TextIO.print ("\n -->  " ^ printconf (e',s') ) ;
          printred' (e',s'))
      | NONE => (TextIO.print "\n -/->  " ; 
                 if valore e then 
                     TextIO.print "(a value)\n" 
                 else 
                     TextIO.print "(stuck - not a value)" )

fun printred (e,s) = (TextIO.print ("      "^(printconf (e,s))) ;
                          printred' (e,s))

