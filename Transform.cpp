#include <clang/Tooling/Tooling.h>
#include <clang/Sema/SemaConsumer.h>
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
    UPCRDecls(ASTContext& Context, DeclContext *DC) {
      QualType argTypes[] = { Context.IntTy, Context.IntTy };
      QualType Ty = Context.getFunctionType(Context.VoidTy, argTypes, 2, FunctionProtoType::ExtProtoInfo());
      upcr_notify = FunctionDecl::Create(Context, DC, SourceLocation(), SourceLocation(), DeclarationName(&Context.Idents.get("upcr_notify")), Ty, Context.getTrivialTypeSourceInfo(Ty));
    }
  };

  class RemoveUPCTransform : public clang::TreeTransform<RemoveUPCTransform> {
  public:
    RemoveUPCTransform(Sema& S, UPCRDecls* D) : TreeTransform(S), Decls(D) {
      AlwaysRebuild();
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
    Decl *TransformDefinition(SourceLocation Loc, Decl *D) {
      if(TranslationUnitDecl *TUD = dyn_cast<TranslationUnitDecl>(D)) {
	return TransformTranslationUnitDecl(TUD);
      } else {
	return TreeTransform::TransformDefinition(Loc, D);
      }
    }
    Decl *TransformTranslationUnitDecl(TranslationUnitDecl *D) {
      TranslationUnitDecl *result = TranslationUnitDecl::Create(SemaRef.Context);
      CopyDeclContext(D, result);
      return result;
    }
    UPCRDecls *Decls;
    void CopyDeclContext(DeclContext *Src, DeclContext *Dst) {
      for(DeclContext::decl_iterator iter = Src->decls_begin(),
          end = Src->decls_end(); iter != end; ++iter) {
	Dst->addDecl(TransformDefinition(SourceLocation(), *iter));
      }
    }
  };

  class RemoveUPCConsumer : public clang::SemaConsumer {
  public:
    RemoveUPCConsumer() : filename("upc.c") {}
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
      TranslationUnitDecl *top = Context.getTranslationUnitDecl();
      UPCRDecls Decls(Context, top);
      RemoveUPCTransform Trans(*S, &Decls);
      Decl *Result = top;
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
