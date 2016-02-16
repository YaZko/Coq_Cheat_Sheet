<div id="table-of-contents">
<h2>Table of Contents</h2>
<div id="text-table-of-contents">
<ul>
<li><a href="#orgheadline7">1. Computation</a>
<ul>
<li><a href="#orgheadline4">1.1. Eval</a>
<ul>
<li><a href="#orgheadline1">1.1.1. Compute</a></li>
<li><a href="#orgheadline2">1.1.2. cbv</a></li>
<li><a href="#orgheadline3">1.1.3. cbn (8.5)</a></li>
</ul>
</li>
<li><a href="#orgheadline5">1.2. Simpl</a></li>
<li><a href="#orgheadline6">1.3. Reflexivity</a></li>
</ul>
</li>
<li><a href="#orgheadline10">2. Intro patterns</a>
<ul>
<li><a href="#orgheadline8">2.1. With square brackets</a></li>
<li><a href="#orgheadline9">2.2. Tricks</a></li>
</ul>
</li>
<li><a href="#orgheadline13">3. Notations</a>
<ul>
<li><a href="#orgheadline11">3.1. Precedence levels</a></li>
<li><a href="#orgheadline12">3.2. Associativity</a></li>
</ul>
</li>
<li><a href="#orgheadline14">4. The Case tactic</a></li>
<li><a href="#orgheadline17">5. Arguments</a>
<ul>
<li><a href="#orgheadline15">5.1. Implicit arguments</a></li>
<li><a href="#orgheadline16">5.2. Arguments renaming</a></li>
</ul>
</li>
<li><a href="#orgheadline18">6. Generalize dependent versus generalize versus revert</a></li>
<li><a href="#orgheadline21">7. Duplicating an hypothesis</a>
<ul>
<li><a href="#orgheadline19">7.1. With remember</a></li>
<li><a href="#orgheadline20">7.2. With generalize dependent</a></li>
</ul>
</li>
<li><a href="#orgheadline28">8. Working with Ltac</a>
<ul>
<li><a href="#orgheadline24">8.1. Matching on hypotheses and conclusions</a>
<ul>
<li><a href="#orgheadline22">8.1.1. Hypotheses</a></li>
<li><a href="#orgheadline23">8.1.2. Conclusions</a></li>
</ul>
</li>
<li><a href="#orgheadline25">8.2. Generate fresh names</a></li>
<li><a href="#orgheadline26">8.3. Print Ltac</a></li>
<li><a href="#orgheadline27">8.4. Working with PG</a></li>
</ul>
</li>
</ul>
</div>
</div>

# Computation<a id="orgheadline7"></a>

## Eval<a id="orgheadline4"></a>

### Compute<a id="orgheadline1"></a>

### cbv<a id="orgheadline2"></a>

### cbn (8.5)<a id="orgheadline3"></a>

## Simpl<a id="orgheadline5"></a>

## Reflexivity<a id="orgheadline6"></a>

Reflexivity does more than simpl, it notably tries to unfold definitions. 

# Intro patterns<a id="orgheadline10"></a>

## With square brackets<a id="orgheadline8"></a>

Conjunction: just a list with no separators
Ex: [H1 [H2 H3]] or (H1 & H2 & H3)
Disjunction: |
Ex: [H1 | H2]

## Tricks<a id="orgheadline9"></a>

<- or -> to rewrite directly an equality. 
\_ clear the hypothesis directly
? to let Coq choose the name

# Notations<a id="orgheadline13"></a>

## Precedence levels<a id="orgheadline11"></a>

Go from 0 (tightest) to 100, with an additionnal special 200.

## Associativity<a id="orgheadline12"></a>

No associativity
Left associativity
Right associativity

# The Case tactic<a id="orgheadline14"></a>

From Software Foundation, used to keep track of the ongoing case

\*\*

     Require String. Open Scope string_scope.
    
     Ltac move_to_top x :=
     match reverse goal with
    | H : _ | - _ => try move x after H |
    end.
    
    Tactic Notation "assert_eq" ident(x) constr(v) :=
    let H := fresh in
    assert (x = v) as H by reflexivity;
    clear H.
    
    Tactic Notation "Case_aux" ident(x) constr(name) :=
    first [
    set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].
    
    Tactic Notation "Case" constr(name) := Case_aux Case name.
    Tactic Notation "SCase" constr(name) := Case_aux SCase name.
    Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
    Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
    Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
    Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
    Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
    Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

# Arguments<a id="orgheadline17"></a>

## Implicit arguments<a id="orgheadline15"></a>

Implicit arguments are treated the same way as if provided as an \_, but systematically.
We can declare them at define time by putting curly brackets around the argument.

    Inductive list {A : Type} : Type :=
     | nil : list 
     | cons : A -> list -> list.

Afterwards, through the Arguments directive: name and list of arguments, curly
brackets for the ones to be inferred.

Use an @ to disable implicit arguments locally.

    Definition l : @list nat := ... .

## Arguments renaming<a id="orgheadline16"></a>

Arguments can be used to rename arguments using the rename flag (:rename. at the end of the command).
(PW: explain? example?)

# Generalize dependent versus generalize versus revert<a id="orgheadline18"></a>

Starting from a goal

    a, b : A
    EQ : a = b
    ---------
      b = a

One can use different tactics to move hypotheses from the context to the goal.

    revert EQ
    
    a, b : A
    ---------
    a = b -> b = a

OR

    generalize EQ 
    
    a, b : A
    EQ : a = b
    ---------
    a = b -> b = a

Notice that the generalized hypothesis is still present in the context, contrary to the reverted one.

We can also generalize terms of type in Type.

    generalize a
    
    a, b : A
    EQ : a = b
    ---------
    forall a0: A, b = a0

Here we have lost some information, because the a in the context is no longer related to the new one.
This situation is solved using generalize dependent.

    generalize dependent a
    
    b : A
    ---------
    forall a : A, a = b -> b = a

# Duplicating an hypothesis<a id="orgheadline21"></a>

## With remember<a id="orgheadline19"></a>

    Ltac dup H := 
    let H' := fresh "H" in 
    remember H as H'; clear HeqH'.

## With generalize dependent<a id="orgheadline20"></a>

    Ltac dup H :=
    let H' := fresh "H" in
    generalize dependent H; intros H'.

# Working with Ltac<a id="orgheadline28"></a>

## Matching on hypotheses and conclusions<a id="orgheadline24"></a>

### Hypotheses<a id="orgheadline22"></a>

Looking for an hypothesis of the form P x y, for any x and y.

    match goal with
      H : P ?x ?y |- _ => destruct H; auto
    end.

This will fail if no such hypothesis exists.
You can add `try` in front of it.

To match **all** such hypotheses, add `repeat`.

The following example shows how to use hypotheses matching to remove duplicates in hypotheses.

    Goal P x y -> P x y -> P x z -> P x z -> P x z -> P y z.
    Proof.
      intros.
    
      repeat match goal with
        H1 : P ?x ?y,
            H2: P ?x ?y |- _ => clear H1
      end.
    Qed.

We try to match two hypotheses of the form P ?x ?y. The pattern matching is
 strong enough to express that H1 and H2 must refer to the same x and y.
H1 and H2 are guaranteed to be different though.

It is also possible to match part of an hypothesis.
Using `context`:

    match goal with
      H : context [P ?x ?y] |- _ => (* do stuff *)
    end.

### Conclusions<a id="orgheadline23"></a>

The matching can also be made on the conlusion of the goal (after `|-`):

    match goal with
      |- context [P ?x ?y] => (* do stuff *)
    end.

Of course, multiple patterns can be matched.

    repeat match goal with
      H : context [P ?x ?y] |- _ => (* do stuff *)
    | |- context [P ?x ?y] => (* do stuff *)
    end.

This will loop as long as either the hypotheses or the conclusion contain a term matching `P ?x ?y`.
Be sure to remove the matching hypotheses to enforce termination.

## Generate fresh names<a id="orgheadline25"></a>

Sometimes we need to generate fresh names inside tactics (see [7](#orgheadline21))

    let n := fresh in (* generate new name, probably H0, H1, H2 *)
    intro n
    
    let n := fresh H in (* generate new name, based on the name of H *)
    intro n
    
    let n := fresh "H" in (* generate new name, based on the given string "H" *)
    intro n

## Print Ltac<a id="orgheadline26"></a>

One can view the Ltac code of a tactic (when it's actually written in Ltac).

    Print Ltac inv.
    
    --->
    Ltac inv H := inversion H; clear H; subst

## Working with PG<a id="orgheadline27"></a>

One can add custom keybindings to Emacs / PG.
For example, to see the Ltac code of a tactic (see previous section), we can define the following Emacs lisp code in the appropriate file (~/.emacs= in my case)

    (defun coq-Print-Ltac (withprintingall)
      "Ask for a tactic and Print Ltac it."
      (interactive "P")
      (if withprintingall
          (coq-ask-do-show-all "Print Ltac" "Print Ltac")
        (coq-ask-do "Print Ltac" "Print Ltac")))
    
    (global-set-key (kbd "C-c C-$") 'coq-Print-Ltac)

(PW: I should investigate what occurences of "Print Ltac" stand for what)