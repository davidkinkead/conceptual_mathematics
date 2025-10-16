/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace ConceptualMathematics

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

/--
Lean code that is saved to the examples file.
-/
@[code_block savedLean]
def savedLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote (code.getString))) #[$underlying])

/--
An import of some other module, to be located in the saved code. Not rendered.
-/
@[code_block]
def savedImport : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])

/--
Comments to be added as module docstrings to the examples file.
-/
@[code_block]
def savedComment : CodeBlockExpanderOf Unit
  | (), code => do
    let str := code.getString.trimRight
    let comment := s!"/-!\n{str}\n-/"
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])



/-
Custom extensions
-/

/- HTML tag: span -/

inline_extension Inline.htmlSpan («class» : String) where
  data := .str «class»
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun goI _ data contents => do
      let .str «class» := data
        | HtmlT.logError "Expected JSON string" *> pure .empty
      pure {{<span class={{«class»}}>{{← contents.mapM goI}}</span>}}

structure ClassArgs where
  «class» : String

section
variable [Monad m] [MonadError m]
instance : FromArgs ClassArgs m where
  fromArgs := ClassArgs.mk <$> .named `«class» .string false
end

@[role]
def htmlSpan : RoleExpanderOf ClassArgs
  | {«class»}, stxs => do
    let contents ← stxs.mapM elabInline
    ``(Inline.other (Inline.htmlSpan $(quote «class»)) #[$contents,*])


/- HTML tag: div -/

block_extension Block.htmlDiv («class» : String) where
  data := .str «class»
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .str «class» := data
        | HtmlT.logError "Expected JSON string" *> pure .empty
      pure {{<div class={{«class»}}>{{← contents.mapM goB}}</div>}}

@[directive]
def htmlDiv : DirectiveExpanderOf ClassArgs
  | {«class»}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.htmlDiv $(quote «class»)) #[ $contents,* ])


/- HTML tag: details -/

block_extension Block.htmlDetails (classDetails : String) (classSummary : String) (summary : String) where
  data := .arr #[.str classDetails, .str classSummary, .str summary]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .arr #[.str classDetails, .str classSummary, .str summary] := data
        | HtmlT.logError "Expected three-element JSON array of strings" *> pure .empty
      pure {{<details class={{classDetails}}><summary class={{classSummary}}>{{summary}}</summary>{{← contents.mapM goB}}</details>}}

structure DetailsArgs where
  classDetails : String
  classSummary : String
  summary : String

section
variable [Monad m] [MonadError m]
instance : FromArgs DetailsArgs m where
  fromArgs := DetailsArgs.mk <$> .named `classDetails .string false <*> .named `classSummary .string false <*> .named `summary .string false
end

@[directive]
def htmlDetails : DirectiveExpanderOf DetailsArgs
  | {classDetails, classSummary, summary}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.htmlDetails $(quote classDetails) $(quote classSummary) $(quote summary)) #[ $contents,* ])


/- definition -/

block_extension Block.definition (definitionTerm : String) (definitionPage : String) where
  data := .arr #[.str definitionTerm, .str definitionPage]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .arr #[.str definitionTerm, .str definitionPage] := data
        | HtmlT.logError "Expected two-element JSON array of strings" *> pure .empty
      pure {{<div class={{"definition"}}><span class={{"definitionTerm"}}>{{"Definition: " ++ definitionTerm}}</span><span class={{"definitionPage"}}>{{"&emsp;(p. " ++ definitionPage ++ ")"}}</span>{{← contents.mapM goB}}</div>}}

structure DefinitionArgs where
  definitionTerm : String
  definitionPage : String

section
variable [Monad m] [MonadError m]
instance : FromArgs DefinitionArgs m where
  fromArgs := DefinitionArgs.mk <$> .named `definitionTerm .string false <*> .named `definitionPage .string false
end

@[directive]
def definition : DirectiveExpanderOf DefinitionArgs
  | {definitionTerm, definitionPage}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.definition $(quote definitionTerm) $(quote definitionPage)) #[ $contents,* ])


/- excerpt -/

block_extension Block.excerpt (excerptPage : String) where
  data := .str excerptPage
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .str excerptPage := data
        | HtmlT.logError "Expected JSON string" *> pure .empty
      pure {{<div class={{"excerpt"}}><span class={{"excerptTitle"}}>{{"Excerpt"}}</span><span class={{"excerptPage"}}>{{"&emsp;(p. " ++ excerptPage ++ ")"}}</span>{{← contents.mapM goB}}</div>}}

structure ExcerptArgs where
  excerptPage : String

section
variable [Monad m] [MonadError m]
instance : FromArgs ExcerptArgs m where
  fromArgs := ExcerptArgs.mk <$> .named `excerptPage .string false
end

@[directive]
def excerpt : DirectiveExpanderOf ExcerptArgs
  | {excerptPage}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.excerpt $(quote excerptPage)) #[ $contents,* ])


/- question -/

block_extension Block.question (questionTitle : String) (questionPage : String) where
  data := .arr #[.str questionTitle, .str questionPage]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .arr #[.str questionTitle, .str questionPage] := data
        | HtmlT.logError "Expected two-element JSON array of strings" *> pure .empty
      pure {{<div class={{"question"}}><span class={{"questionTitle"}}>{{questionTitle}}</span><span class={{"questionPage"}}>{{"&emsp;(p. " ++ questionPage ++ ")"}}</span>{{← contents.mapM goB}}</div>}}

structure QuestionArgs where
  questionTitle : String
  questionPage : String

section
variable [Monad m] [MonadError m]
instance : FromArgs QuestionArgs m where
  fromArgs := QuestionArgs.mk <$> .named `questionTitle .string false <*> .named `questionPage .string false
end

@[directive]
def question : DirectiveExpanderOf QuestionArgs
  | {questionTitle, questionPage}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.question $(quote questionTitle) $(quote questionPage)) #[ $contents,* ])


/- solution -/

structure SolutionArgs where
  solutionTo : String

section
variable [Monad m] [MonadError m]
instance : FromArgs SolutionArgs m where
  fromArgs := SolutionArgs.mk <$> .named `solutionTo .string false
end

@[directive]
def solution : DirectiveExpanderOf SolutionArgs
  | {solutionTo}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.htmlDetails $(quote "solution") $(quote "solution") $(quote <| "Solution: " ++ solutionTo)) #[ $contents,* ])


/- theorem -/

structure TheoremArgs where
  theoremTitle : String
  theoremPage : String

section
variable [Monad m] [MonadError m]
instance : FromArgs TheoremArgs m where
  fromArgs := TheoremArgs.mk <$> .named `theoremTitle .string false <*> .named `theoremPage .string false
end

@[directive]
def theoremDirective : DirectiveExpanderOf TheoremArgs
  | {theoremTitle, theoremPage}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.question $(quote theoremTitle) $(quote theoremPage)) #[ $contents,* ])


/- proof -/

block_extension Block.proof (proofPage : String) where
  data := .str proofPage
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some fun _ goB _ data contents => do
      let .str proofPage := data
        | HtmlT.logError "Expected JSON string" *> pure .empty
      pure {{<div class={{"proof"}}><span class={{"proofTitle"}}>{{"Proof"}}</span><span class={{"proofPage"}}>{{"&emsp;(p. " ++ proofPage ++ ")"}}</span>{{← contents.mapM goB}}</div>}}

structure ProofArgs where
  proofPage : String

section
variable [Monad m] [MonadError m]
instance : FromArgs ProofArgs m where
  fromArgs := ProofArgs.mk <$> .named `proofPage .string false
end

@[directive]
def proof : DirectiveExpanderOf ProofArgs
  | {proofPage}, stxs => do
    let contents ← stxs.mapM elabBlock
    ``(Block.other (Block.proof $(quote proofPage)) #[ $contents,* ])

end ConceptualMathematics
