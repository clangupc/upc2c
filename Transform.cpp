#include <clang/Tooling/Tooling.h>
#include <clang/Sema/SemaConsumer.h>
#include <clang/Sema/Scope.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <llvm/Support/raw_ostream.h>
#include <string>
#include "../../lib/Sema/TreeTransform.h"

using namespace clang;
using namespace clang::tooling;
using llvm::APInt;

namespace {

  struct UPCRDecls {
    FunctionDecl * upcr_notify;
    explicit UPCRDecls(ASTContext& Context) {
      DeclContext *DC = Context.getTranslationUnitDecl();
      QualType argTypes[] = { Context.IntTy, Context.IntTy };
      QualType Ty = Context.getFunctionType(Context.VoidTy, argTypes, 2, FunctionProtoType::ExtProtoInfo());
      upcr_notify = FunctionDecl::Create(Context, DC, SourceLocation(), SourceLocation(), DeclarationName(&Context.Idents.get("upcr_notify")), Ty, Context.getTrivialTypeSourceInfo(Ty));
      llvm::SmallVector<ParmVarDecl *, 2> Params;
      Params.push_back(ParmVarDecl::Create(Context, upcr_notify, SourceLocation(), SourceLocation(), 0, Context.IntTy, 0, SC_None, SC_None, 0));
      Params.push_back(ParmVarDecl::Create(Context, upcr_notify, SourceLocation(), SourceLocation(), 0, Context.IntTy, 0, SC_None, SC_None, 0));
      Params[0]->setScopeInfo(0, 0);
      Params[0]->setScopeInfo(0, 1);
      upcr_notify->setParams(Params);
    }
  };

  class RemoveUPCTransform : public clang::TreeTransform<RemoveUPCTransform> {
  public:
    RemoveUPCTransform(Sema& S, UPCRDecls* D) : TreeTransform(S), Decls(D) {
      AlwaysRebuild();
    }
    // TreeTransform ignores AlwayRebuild for literals
    ExprResult TransformIntegerLiteral(IntegerLiteral *E) {
      return IntegerLiteral::Create(SemaRef.Context, E->getValue(), E->getType(), E->getLocation());
    }
    ExprResult BuildUPCRCall(FunctionDecl *FD, std::vector<Expr*>& args) {
      ExprResult Fn = SemaRef.BuildDeclRefExpr(FD, FD->getType(), VK_LValue, SourceLocation());
      return SemaRef.BuildResolvedCallExpr(Fn.get(), FD, SourceLocation(), args.data(), args.size(), SourceLocation());
    }
    StmtResult TransformUPCNotifyStmt(UPCNotifyStmt *S) {
      Expr *ID = S->getIdValue();
      std::vector<Expr*> args;
      if(ID) {
	args.push_back(TransformExpr(ID).get());
	args.push_back(IntegerLiteral::Create(
	  SemaRef.Context, APInt(32, 0), SemaRef.Context.IntTy, SourceLocation()));
      } else {
	args.push_back(IntegerLiteral::Create(
	  SemaRef.Context, APInt(32, 0), SemaRef.Context.IntTy, SourceLocation()));
	args.push_back(IntegerLiteral::Create(
	  SemaRef.Context, APInt(32, 1), SemaRef.Context.IntTy, SourceLocation()));
      }
      Stmt *result = BuildUPCRCall(Decls->upcr_notify, args).get();
      return SemaRef.Owned(result);
    }
    Decl *TransformDecl(SourceLocation Loc, Decl *D) {
      return TreeTransform::TransformDecl(Loc, D);
    }
    Decl *TransformDeclaration(Decl *D, DeclContext *DC) {
      if(TranslationUnitDecl *TUD = dyn_cast<TranslationUnitDecl>(D)) {
	return TransformTranslationUnitDecl(TUD);
      } else if(FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
	FunctionDecl *result = FunctionDecl::Create(SemaRef.Context, DC, FD->getLocStart(),
				    FD->getNameInfo(), TransformType(FD->getType()),
				    TransformType(FD->getTypeSourceInfo()),
				    FD->getStorageClass(), FD->getStorageClassAsWritten(),
				    FD->isInlineSpecified(), FD->hasWrittenPrototype(),
				    FD->isConstexpr());
	if(FD->doesThisDeclarationHaveABody()) {
	  SemaRef.ActOnStartOfFunctionDef(0, result);
	  Sema::ContextRAII savedContext(SemaRef, result);
	  SemaRef.ActOnFinishFunctionBody(result, TransformStmt(FD->getBody()).get());
	}
	return result;
      } else if(VarDecl *VD = dyn_cast<VarDecl>(D)) {
	VarDecl *result = VarDecl::Create(SemaRef.Context, DC, VD->getLocStart(), VD->getLocation(), VD->getIdentifier(),
			       TransformType(VD->getType()), TransformType(VD->getTypeSourceInfo()),
			       VD->getStorageClass(), VD->getStorageClassAsWritten());
	if(Expr *Init = VD->getInit()) {
	  result->setInit(TransformExpr(Init).get());
	}
	return result;
      } else if(RecordDecl *RD = dyn_cast<RecordDecl>(D)) {
	return RecordDecl::Create(SemaRef.Context, RD->getTagKind(), DC,
				  RD->getLocStart(), RD->getLocation(),
				  RD->getIdentifier(), cast_or_null<RecordDecl>(TransformDecl(SourceLocation(), RD->getPreviousDecl())));
      } else if(TypedefDecl *TD = dyn_cast<TypedefDecl>(D)) {
	return TypedefDecl::Create(SemaRef.Context, DC, TD->getLocStart(), TD->getLocation(), TD->getIdentifier(), TransformType(TD->getTypeSourceInfo()));
      } else {
	assert(!"Unknown Decl");
      }
    }
    Decl *TransformTranslationUnitDecl(TranslationUnitDecl *D) {
      TranslationUnitDecl *result = SemaRef.Context.getTranslationUnitDecl();
      Scope CurScope(0, Scope::DeclScope, SemaRef.getDiagnostics());
      SemaRef.PushDeclContext(&CurScope, result);
      CopyDeclContext(D, result);
      return result;
    }
    UPCRDecls *Decls;
    void CopyDeclContext(DeclContext *Src, DeclContext *Dst) {
      for(DeclContext::decl_iterator iter = Src->decls_begin(),
          end = Src->decls_end(); iter != end; ++iter) {
	Dst->addDecl(TransformDeclaration(*iter, Dst));
      }
    }
  };

  class RemoveUPCConsumer : public clang::SemaConsumer {
  public:
    RemoveUPCConsumer() : filename("upc.c") {}
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
      TranslationUnitDecl *top = Context.getTranslationUnitDecl();
      // Copy the ASTContext and Sema
      LangOptions LangOpts = Context.getLangOpts();
      ASTContext newContext(LangOpts, Context.getSourceManager(), &Context.getTargetInfo(),
			    Context.Idents, Context.Selectors, Context.BuiltinInfo,
			    Context.getTypes().size());
      ASTConsumer nullConsumer;
      UPCRDecls Decls(newContext);
      Sema newSema(S->getPreprocessor(), newContext, nullConsumer);
      RemoveUPCTransform Trans(newSema, &Decls);
      Decl *Result = Trans.TransformTranslationUnitDecl(top);
      std::string error;
      llvm::raw_fd_ostream OS(filename.c_str(), error);
      Result->print(OS);
    }
    void InitializeSema(Sema& SemaRef) { S = &SemaRef; }
    void ForgetSema() { S = 0; }
  private:
    Sema *S;
    std::string filename;
  };

  class RemoveUPCAction : public clang::ASTFrontendAction {
  public:
    virtual clang::ASTConsumer *CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
      return new RemoveUPCConsumer();
    }
  };

}

int main(int argc, const char ** argv) {
  std::vector<std::string> options(argv, argv + argc);
  FileManager Files((FileSystemOptions()));
  ToolInvocation tool(options, new RemoveUPCAction, &Files);
  tool.run();
}
