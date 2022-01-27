# OVERVIEW: 

Many thanks to our reviewers for their interest and appreciation of certain aspects of our work. 

We acknowledge our weakness in the paper presentation. 
Thanks again for the time and effort in pointing out our typos and giving out constructive suggestionss. 

We took all the valuable comments into account and made the following change list. 


# CHANGE LIST: 


Here is a list of the changes that we plan to make in
response to the reviews and the timeline for those changes.

| Changes     | Description | Timeline    |
| ----------- | ----------- | ----------- |
| Typos       | Thanks They are helpful and much appricated!  | Already Done| 
| Paragraph   |             | Text        |




# RESPONSE: 

## To Reviewer A

### Q1. Which aspects of your formalism build on previous work, and which are novel to this submission?

1. The syntax definition is the first core language for the mixed synchronous/asynchronous paradigm, although both were defined separately before. 

2. Since the syntax combination is new, the operational semantics is built on top of Esterel, so the ones with (Async) (Await) and (Call) are new. 

3. The trace inference rules presented in Sec 5.1 are entirely novel. 

4. For the back-end TRS, in the functions: nullable, first, derivatives, all the definitions for the waiting operator (?) and asynchronous parallel (||) are novels. 

5. The temporal verification framework is novel compared to traditional automata-based model checking. 


### Q2. What were the key technical challenges you faced?

Among all the challenges we faced, implementing the parallel merging algorithm took us the longest. 
The concept of linear synchronous parallelism is not so complicated. 
However, the Kleene stars make it complex. For example 
({A}.{B})^* || ({C}. {D}. {E})^*, we should be able to find a fixpoint, which is 
({A,C}.{B.D}.{A, E}.{B, C}.{A, D}.{B, E})^*. 

Luckily we manage to do that in our final implementation. 

Another surprise is the proof for the loop invariant inference algorithm we discovered, which has not been mentioned by prior works at all!




### Q3. What are the sorts of properties you would like to check in a typical HipHop.js program?

Our proposed specification conveniently fuses traditional linear temporal logics, such as LTL. 

| LTL         | SyncEffs    | Description |
| ----------- | ----------- | ----------- |
| $\mathcal{F} (A)$ | $\{\}^*{\cdot}\{A\}$      | Finially A  (Safty) | 
| $\mathcal{G} (A)$ | $\{A\}^*$      | Globally A (Liveliness) | 
| $A\ \mathcal{U}  B$ | $\{A\}^*{\cdot}\{B\}$ | A until B
| $\mathcal{X} (A)$ | $\{\}{\cdot}\{A\}$  | Next A
| $A \rightarrow B$ | $\{\overline{A}\} \vee \{A, B\}$ |  Implication
| $\mathcal{F\ G} (A)$ | $\{\}^*{\cdot}\{A\}^*$  | Finially globally A
| $\mathcal{G\ F} (A)$ | $(\{\}^*{\cdot}\{A\})^*$  | Globally finially  A

(Here A and B are signals emitted from the program)



### Q4. Were there any surprises or challenges in the implementation/evaluation?

We preferred to make use of existing implementations to build our front-end parser. We looked into the source code of the compiler of Hiphop.js. Unfortunately, we did not manage to get it run. Due to the time limits, we wrote the parser from scratch in Ocaml for the core language. 

If there are follow-up works, we will continue to investigate adding our temporal verification into existing language implementations. 






## To Reviewer B 


### Q1. Can you expand on how you validated the verifier? In particular, what is the nature of the programs used, how they were selected, how were the annotations added.

We chose the program by needs of validating our novel ideas and challenging implementations: 

1. The loop invariant inference (FV-Loop): We proved (by inductive cases in Appendix C) the correctness of the loop invariant inference algorithm. 
2. The Async/Await rules (FV-Await and FV-Async): They are newly proposed in this paper. 
3. The parallel merging algorithm (FV-Par): Although the conceptual synchronous parallel is simple, the implementation is challenging. (Details see the response Q2 To Reviewer A)

Therefore, we chose test cases related to each of the above constructs, and we produced some other test cases involving combinations of the above constructs. 

We annotate the specifications by hand, based on the behaviors defined by the Esterel Compilers. 


### Q2. How are the LHS/RHS from Fig. 9 provided? Are they deduced automatically from the program or do they need to be encoded by the developer?

While verifying a program, the LHS/RHS are deducted automatically from the program. 
The inclusion checkings are triggered: i) before function calls to check precondition; ii) by the end of the
verifying a function to check the postcondition. One example from the paper is Figure 5, step 10. which checks the function postcondition. 

However, one can use the back-end TRS independently. Our implementation includes an inclusion parser, which triggers the TRS directly. 
One example input and its corresponding TRS output:
```
({A, D, C})*.{} \/ {B}.({A})* |- ({})* \/ ({A,B})*;

----------------------------------------
((({A,D,C,})* . {}) . ({A,})*) \/ ({B,} . ({A,})*) |- ({})* \/ ({A,B,})*
[Result] Succeed
[Verification Time: 0.000132 s]
 

* ((({A,D,C,})* . {}) . ({A,})*) \/ ({B,} . ({A,})*) |- ({})* \/ ({A,B,})*   [UNFOLD]
* ├── ({A,})* |- ({})*   [UNFOLD]
* │   └── ({A,})* |- ({})*   [Reoccur]
* ├── ({A,})* |- ({})*   [UNFOLD]
* │   └── ({A,})* |- ({})*   [Reoccur]
* └── ((({A,D,C,})* . {}) . ({A,})*) \/ (emp . ({A,})*) |- ({})*   [UNFOLD]
*     ├── ({A,})* |- ({})*   [UNFOLD]
*     │   └── ({A,})* |- ({})*   [Reoccur]
*     ├── ({A,})* |- ({})*   [UNFOLD]
*     │   └── ({A,})* |- ({})*   [Reoccur]
*     └── (({A,D,C,})* . ({} . ({A,})*)) \/ ({A,})* |- ({})*   [UNFOLD]
*         ├── ({A,})* |- ({})*   [UNFOLD]
*         │   └── ({A,})* |- ({})*   [Reoccur]
*         ├── ({A,})* |- ({})*   [UNFOLD]
*         │   └── ({A,})* |- ({})*   [Reoccur]
*         └── (({A,D,C,})* . ({} . ({A,})*)) \/ ({A,})* |- ({})*   [Reoccur]
```





