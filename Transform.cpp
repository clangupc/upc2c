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
    FunctionDecl * upcr_wait;
    FunctionDecl * upcr_barrier;
    FunctionDecl * upcr_mythread;
    FunctionDecl * upcr_threads;
    FunctionDecl * upcr_hasMyAffinity_pshared;
    FunctionDecl * upcr_hasMyAffinity_shared;
    FunctionDecl * UPCR_BEGIN_FUNCTION;
    FunctionDecl * UPCRT_STARTUP_PSHALLOC;
    FunctionDecl * UPCRT_STARTUP_SHALLOC;
    FunctionDecl * upcr_startup_pshalloc;
    FunctionDecl * upcr_startup_shalloc;
    FunctionDecl * upcr_put_pshared;
    FunctionDecl * upcr_put_shared;
    FunctionDecl * UPCR_GET_PSHARED;
    FunctionDecl * UPCR_PUT_PSHARED;
    FunctionDecl * UPCR_GET_SHARED;
    FunctionDecl * UPCR_PUT_SHARED;
    FunctionDecl * UPCR_ADD_SHARED;
    FunctionDecl * UPCR_GET_PSHARED_STRICT;
    FunctionDecl * UPCR_PUT_PSHARED_STRICT;
    FunctionDecl * UPCR_GET_SHARED_STRICT;
    FunctionDecl * UPCR_PUT_SHARED_STRICT;
    FunctionDecl * UPCR_ADD_PSHAREDI;
    FunctionDecl * UPCR_ADD_PSHARED1;
    FunctionDecl * UPCR_SUB_SHARED;
    FunctionDecl * UPCR_SUB_PSHAREDI;
    FunctionDecl * UPCR_SUB_PSHARED1;
    FunctionDecl * UPCR_ISEQUAL_SHARED_SHARED;
    FunctionDecl * UPCR_ISEQUAL_SHARED_PSHARED;
    FunctionDecl * UPCR_ISEQUAL_PSHARED_SHARED;
    FunctionDecl * UPCR_ISEQUAL_PSHARED_PSHARED;
    VarDecl * upcr_forall_control;
    QualType upcr_shared_ptr_t;
    QualType upcr_pshared_ptr_t;
    QualType upcr_startup_shalloc_t;
    QualType upcr_startup_pshalloc_t;
    SourceLocation FakeLocation;
    explicit UPCRDecls(ASTContext& Context) {
      SourceManager& SourceMgr = Context.getSourceManager();
      FakeLocation = SourceMgr.getLocForStartOfFile(SourceMgr.getMainFileID());

      // types
      upcr_shared_ptr_t = CreateTypedefType(Context, "upcr_shared_ptr_t");
      upcr_pshared_ptr_t = CreateTypedefType(Context, "upcr_pshared_ptr_t");
      upcr_startup_shalloc_t = CreateTypedefType(Context, "upcr_startup_shalloc_t");
      upcr_startup_pshalloc_t = CreateTypedefType(Context, "upcr_startup_pshalloc_t");

      // upcr_notify
      {
	QualType argTypes[] = { Context.IntTy, Context.IntTy };
	upcr_notify = CreateFunction(Context, "upcr_notify", Context.VoidTy, argTypes, 2);
      }
      // upcr_wait
      {
	QualType argTypes[] = { Context.IntTy, Context.IntTy };
	upcr_wait = CreateFunction(Context, "upcr_wait", Context.VoidTy, argTypes, 2);
      }
      // upcr_barrier
      {
	QualType argTypes[] = { Context.IntTy, Context.IntTy };
	upcr_barrier = CreateFunction(Context, "upcr_barrier", Context.VoidTy, argTypes, 2);
      }
      // upcr_mythread
      {
	upcr_mythread = CreateFunction(Context, "upcr_mythread", Context.IntTy, 0, 0);
      }
      // upcr_threads
      {
	upcr_threads = CreateFunction(Context, "upcr_threads", Context.IntTy, 0, 0);
      }
      // upcr_hasMyAffinity_pshared
      {
	QualType argTypes[] = { upcr_pshared_ptr_t };
	upcr_hasMyAffinity_pshared = CreateFunction(Context, "upcr_hasMyAffinity_pshared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_hasMyAffinity_shared
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	upcr_hasMyAffinity_shared = CreateFunction(Context, "upcr_hasMyAffinity_shared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_put_pshared
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.VoidPtrTy, Context.IntTy };
	upcr_put_pshared = CreateFunction(Context, "upcr_put_pshared", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_put_shared
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.VoidPtrTy, Context.IntTy };
	upcr_put_shared = CreateFunction(Context, "upcr_put_shared", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_GET_PSHARED
      {
	QualType argTypes[] = { Context.VoidPtrTy, upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_PSHARED = CreateFunction(Context, "UPCR_GET_PSHARED", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PUT_PSHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.VoidPtrTy, Context.IntTy, Context.IntTy };
	UPCR_PUT_PSHARED = CreateFunction(Context, "UPCR_PUT_PSHARED", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_GET_SHARED
      {
	QualType argTypes[] = { Context.VoidPtrTy, upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_SHARED = CreateFunction(Context, "UPCR_GET_SHARED", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PUT_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.VoidPtrTy, Context.IntTy, Context.IntTy };
	UPCR_PUT_SHARED = CreateFunction(Context, "UPCR_PUT_SHARED", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_GET_PSHARED_STRICT
      {
	QualType argTypes[] = { Context.VoidPtrTy, upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_PSHARED_STRICT = CreateFunction(Context, "UPCR_GET_PSHARED_STRICT", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PUT_PSHARED_STRICT
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.VoidPtrTy, Context.IntTy, Context.IntTy };
	UPCR_PUT_PSHARED_STRICT = CreateFunction(Context, "UPCR_PUT_PSHARED_STRICT", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_GET_SHARED_STRICT
      {
	QualType argTypes[] = { Context.VoidPtrTy, upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_SHARED_STRICT = CreateFunction(Context, "UPCR_GET_SHARED_STRICT", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PUT_SHARED_STRICT
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.VoidPtrTy, Context.IntTy, Context.IntTy };
	UPCR_PUT_SHARED_STRICT = CreateFunction(Context, "UPCR_PUT_SHARED_STRICT", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADD_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.IntTy, Context.IntTy };
	UPCR_ADD_SHARED = CreateFunction(Context, "UPCR_ADD_SHARED", upcr_shared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADD_PSHAREDI
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_ADD_PSHAREDI = CreateFunction(Context, "UPCR_ADD_PSHAREDI", upcr_pshared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADD_PSHARED1
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_ADD_PSHARED1 = CreateFunction(Context, "UPCR_ADD_PSHARED1", upcr_pshared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_SUB_SHARED = CreateFunction(Context, "UPCR_SUB_SHARED", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_PSHAREDI
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t, Context.IntTy };
	UPCR_SUB_PSHAREDI = CreateFunction(Context, "UPCR_SUB_PSHAREDI", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_PSHARED1
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t, Context.IntTy };
	UPCR_SUB_PSHARED1 = CreateFunction(Context, "UPCR_SUB_PSHARED1", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_SHARED_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_shared_ptr_t };
	UPCR_ISEQUAL_SHARED_SHARED = CreateFunction(Context, "UPCR_ISEQUAL_SHARED_SHARED", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_SHARED_PSHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_pshared_ptr_t };
	UPCR_ISEQUAL_SHARED_PSHARED = CreateFunction(Context, "UPCR_ISEQUAL_SHARED_PSHARED", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_PSHARED_SHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_shared_ptr_t };
	UPCR_ISEQUAL_PSHARED_SHARED = CreateFunction(Context, "UPCR_ISEQUAL_PSHARED_SHARED", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_PSHARED_PSHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t };
	UPCR_ISEQUAL_PSHARED_PSHARED = CreateFunction(Context, "UPCR_ISEQUAL_PSHARED_PSHARED", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_BEGIN_FUNCTION
      {
	UPCR_BEGIN_FUNCTION = CreateFunction(Context, "UPCR_BEGIN_FUNCTION", Context.VoidTy, NULL, 0);
      }
      // UPCRT_STARTUP_PSHALLOC
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy, Context.IntTy, Context.IntTy, Context. getPointerType(Context.getConstType(Context.CharTy)) };
	UPCRT_STARTUP_PSHALLOC = CreateFunction(Context, "UPCRT_STARTUP_PSHALLOC", upcr_startup_pshalloc_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCRT_STARTUP_SHALLOC
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.IntTy, Context.IntTy, Context.IntTy, Context. getPointerType(Context.getConstType(Context.CharTy)) };
	UPCRT_STARTUP_SHALLOC = CreateFunction(Context, "UPCRT_STARTUP_SHALLOC", upcr_startup_shalloc_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_startup_pshalloc
      {
	QualType argTypes[] = { Context.getPointerType(upcr_startup_pshalloc_t), Context.IntTy };
	upcr_startup_pshalloc = CreateFunction(Context, "upcr_startup_pshalloc", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_startup_shalloc
      {
	QualType argTypes[] = { Context.getPointerType(upcr_startup_shalloc_t), Context.IntTy };
	upcr_startup_shalloc = CreateFunction(Context, "upcr_startup_shalloc", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // upcr_forall_control
      {
	DeclContext *DC = Context.getTranslationUnitDecl();
	upcr_forall_control = VarDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get("upcr_forall_control"), Context.IntTy, Context.getTrivialTypeSourceInfo(Context.IntTy), SC_Extern, SC_Extern);
      }

    }
    FunctionDecl *CreateFunction(ASTContext& Context, StringRef name, QualType RetType, QualType * argTypes, int numArgs) {
      DeclContext *DC = Context.getTranslationUnitDecl();
      QualType Ty = Context.getFunctionType(RetType, argTypes, numArgs, FunctionProtoType::ExtProtoInfo());
      FunctionDecl *Result = FunctionDecl::Create(Context, DC, FakeLocation, FakeLocation, DeclarationName(&Context.Idents.get(name)), Ty, Context.getTrivialTypeSourceInfo(Ty));
      llvm::SmallVector<ParmVarDecl *, 4> Params;
      for(int i = 0; i < numArgs; ++i) {
	Params.push_back(ParmVarDecl::Create(Context, Result, SourceLocation(), SourceLocation(), 0, argTypes[i], 0, SC_None, SC_None, 0));
	Params[i]->setScopeInfo(0, i);
      }
      Result->setParams(Params);
      return Result;
    }
    QualType CreateTypedefType(ASTContext& Context, StringRef name) {
      DeclContext *DC = Context.getTranslationUnitDecl();
      RecordDecl *Result = RecordDecl::Create(Context, TTK_Struct, DC,
					      SourceLocation(), SourceLocation(),
					      0);
      Result->startDefinition();
      Result->completeDefinition();
      TypedefDecl *Typedef = TypedefDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get(name), Context.getTrivialTypeSourceInfo(Context.getRecordType(Result)));
      return Context.getTypedefType(Typedef);
    }
  };

  class RemoveUPCTransform : public clang::TreeTransform<RemoveUPCTransform> {
  public:
    RemoveUPCTransform(Sema& S, UPCRDecls* D) : TreeTransform(S), Decls(D) {
    }
    bool AlwaysRebuild() { return true; }
    ExprResult BuildParens(Expr * E) {
      return SemaRef.ActOnParenExpr(SourceLocation(), SourceLocation(), E);
    }
    ExprResult BuildComma(Expr * LHS, Expr * RHS) {
      return SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Comma, LHS, RHS);
    }
    // TreeTransform ignores AlwayRebuild for literals
    ExprResult TransformIntegerLiteral(IntegerLiteral *E) {
      return IntegerLiteral::Create(SemaRef.Context, E->getValue(), E->getType(), E->getLocation());
    }
    ExprResult BuildUPCRCall(FunctionDecl *FD, std::vector<Expr*>& args) {
      ExprResult Fn = SemaRef.BuildDeclRefExpr(FD, FD->getType(), VK_LValue, SourceLocation());
      return SemaRef.BuildResolvedCallExpr(Fn.get(), FD, SourceLocation(), args.data(), args.size(), SourceLocation());
    }
    ExprResult BuildUPCRDeclRef(VarDecl *VD) {
      return SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation());
    }
    Expr * CreateSimpleDeclRef(VarDecl *VD) {
      return SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation()).get();
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
    StmtResult TransformUPCWaitStmt(UPCWaitStmt *S) {
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
      Stmt *result = BuildUPCRCall(Decls->upcr_wait, args).get();
      return SemaRef.Owned(result);
    }
    StmtResult TransformUPCBarrierStmt(UPCBarrierStmt *S) {
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
      Stmt *result = BuildUPCRCall(Decls->upcr_barrier, args).get();
      return SemaRef.Owned(result);
    }
    ExprResult TransformImplicitCastExpr(ImplicitCastExpr *E) {
      if(E->getCastKind() == CK_LValueToRValue && E->getSubExpr()->getType().getQualifiers().hasShared()) {
	return BuildUPCRLoad(TransformExpr(E->getSubExpr()).get(), TransformType(E->getType()), E->getSubExpr()->getType());
      } else {
	// We can't use the default transform, because it
	// strips off all implicit casts.  We may need to
	// process the subexpression
	return TransformExpr(E->getSubExpr());
      }
    }
    bool isPointerToShared(QualType Ty) {
      if(const PointerType * PTy = Ty->getAs<PointerType>()) {
	return PTy->getPointeeType().getQualifiers().hasShared();
      } else {
	return false;
      }
    }
    IntegerLiteral *CreateInteger(QualType Ty, int Value) {
      return IntegerLiteral::Create(SemaRef.Context, APInt(SemaRef.Context.getTypeSize(Ty), Value), Ty, SourceLocation());
    }
    ExprResult BuildUPCRLoad(Expr * E, QualType ResultType, QualType Ty) {
      std::pair<Expr *, Expr *> LoadAndVar = BuildUPCRLoadParts(E, ResultType, Ty);
      return BuildParens(BuildComma(LoadAndVar.first, LoadAndVar.second).get());
    }
    // Returns a pair containing the load stmt and a declrefexpr to the
    // temporary variable created.
    std::pair<Expr *, Expr *> BuildUPCRLoadParts(Expr * E, QualType ResultType, QualType Ty) {
      int SizeTypeSize = SemaRef.Context.getTypeSize(SemaRef.Context.getSizeType());
      Qualifiers Quals = Ty.getQualifiers();
      bool Phaseless = isPhaseless(Ty);
      bool Strict = Quals.hasStrict();
      // Select the correct function to call
      FunctionDecl *Accessor;
      if(Phaseless) {
	if(Strict) {
	  Accessor = Decls->UPCR_GET_PSHARED_STRICT;
	} else {
	  Accessor = Decls->UPCR_GET_PSHARED;
	}
      } else {
	if(Strict) {
	  Accessor = Decls->UPCR_GET_SHARED_STRICT;
	} else {
	  Accessor = Decls->UPCR_GET_SHARED;
	}
      }
      VarDecl *TmpVar = CreateTmpVar(ResultType);
      // FIXME: Handle other layout qualifiers
      std::vector<Expr*> args;
      args.push_back(SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, SemaRef.BuildDeclRefExpr(TmpVar, ResultType, VK_LValue, SourceLocation()).get()).get());
      args.push_back(E);
      // offset
      args.push_back(IntegerLiteral::Create(SemaRef.Context, APInt(SizeTypeSize, 0), SemaRef.Context.getSizeType(), SourceLocation()));
      // size
      args.push_back(IntegerLiteral::Create(SemaRef.Context, APInt(SizeTypeSize, SemaRef.Context.getTypeSizeInChars(E->getType()).getQuantity()), SemaRef.Context.getSizeType(), SourceLocation()));
      Expr *Load = BuildUPCRCall(Accessor, args).get();
      return std::make_pair(Load, SemaRef.BuildDeclRefExpr(TmpVar, ResultType, VK_LValue, SourceLocation()).get());
    }
    ExprResult BuildUPCRStore(Expr * LHS, Expr * RHS, QualType Ty, bool ReturnValue = true) {
      int SizeTypeSize = SemaRef.Context.getTypeSize(SemaRef.Context.getSizeType());
      Qualifiers Quals = Ty.getQualifiers(); 
      bool Phaseless = isPhaseless(Ty);
      bool Strict = Quals.hasStrict();
      // Select the correct function to call
      FunctionDecl *Accessor;
      if(Phaseless) {
	if(Strict) {
	  Accessor = Decls->UPCR_PUT_PSHARED_STRICT;
	} else {
	  Accessor = Decls->UPCR_PUT_PSHARED;
	}
      } else {
	if(Strict) {
	  Accessor = Decls->UPCR_PUT_SHARED_STRICT;
	} else {
	  Accessor = Decls->UPCR_PUT_SHARED;
	}
      }
      VarDecl *TmpVar = CreateTmpVar(RHS->getType());
      Expr *SetTmp = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, SemaRef.BuildDeclRefExpr(TmpVar, RHS->getType(), VK_LValue, SourceLocation()).get(), RHS).get();
      std::vector<Expr*> args;
      args.push_back(LHS);
      args.push_back(SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, SemaRef.BuildDeclRefExpr(TmpVar, RHS->getType(), VK_LValue, SourceLocation()).get()).get());
      // offset
      args.push_back(IntegerLiteral::Create(SemaRef.Context, APInt(SizeTypeSize, 0), SemaRef.Context.getSizeType(), SourceLocation()));
      // size
      args.push_back(IntegerLiteral::Create(SemaRef.Context, APInt(SizeTypeSize, SemaRef.Context.getTypeSizeInChars(RHS->getType()).getQuantity()), SemaRef.Context.getSizeType(), SourceLocation()));
      Expr *Store = BuildUPCRCall(Accessor, args).get();
      Expr *CommaRHS = Store;
      if(ReturnValue) {
	CommaRHS = BuildComma(Store, SemaRef.BuildDeclRefExpr(TmpVar, RHS->getType(), VK_LValue, SourceLocation()).get()).get();
      }
      return BuildParens(BuildComma(SetTmp, CommaRHS).get());
    }
    ExprResult TransformUnaryOperator(UnaryOperator *E) {
      QualType ArgType = E->getSubExpr()->getType();
      if((E->getOpcode() == UO_Deref && isPointerToShared(ArgType)) ||
	 (E->getOpcode() == UO_AddrOf && isPointerToShared(E->getType()))) {
	// Strip off * and &.  shared lvalues and pointers-to-shared
	// have the same representation.
	return TransformExpr(E->getSubExpr());
      } else if(ArgType.getQualifiers().hasShared() && E->isIncrementDecrementOp()) {
	bool Phaseless = isPhaseless(ArgType);
	QualType PtrType = Phaseless? Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	VarDecl * TmpPtrDecl = CreateTmpVar(PtrType);
	Expr * TmpPtr = SemaRef.BuildDeclRefExpr(TmpPtrDecl, PtrType, VK_LValue, SourceLocation()).get();
	Expr * SaveArg = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr, BuildParens(TransformExpr(E->getSubExpr()).get()).get()).get();
	std::pair<Expr *, Expr *> Load = BuildUPCRLoadParts(TmpPtr, TransformType(ArgType.getUnqualifiedType()), ArgType);
	Expr * LoadExpr = Load.first;
	Expr * LoadVar = Load.second;
	Expr * NewVal = SemaRef.CreateBuiltinBinOp(SourceLocation(), E->isIncrementOp()?BO_Add:BO_Sub, LoadVar, CreateInteger(SemaRef.Context.IntTy, 1)).get();

	if(E->isPrefix()) {
	  Expr * Result = BuildUPCRStore(TmpPtr, NewVal, ArgType).get();
	  return BuildParens(BuildComma(SaveArg, BuildComma(LoadExpr, Result).get()).get());
	} else {
	  Expr * Result = BuildUPCRStore(TmpPtr, NewVal, ArgType, false).get();
	  return BuildParens(BuildComma(SaveArg, BuildComma(LoadExpr, BuildComma(Result, LoadVar).get()).get()).get());
	}
      } else {
	return TreeTransform::TransformUnaryOperator(E);
      }
    }
    ExprResult TransformBinaryOperator(BinaryOperator *E) {
      // Catch assignment to shared variables
      if(E->getOpcode() == BO_Assign && E->getLHS()->getType().getQualifiers().hasShared()) {
	Expr *LHS = TransformExpr(E->getLHS()).get();
	Expr *RHS = TransformExpr(E->getRHS()).get();
	return BuildUPCRStore(LHS, RHS, E->getLHS()->getType());
      } else {
	Expr *LHS = E->getLHS();
	Expr *RHS = E->getRHS();
	bool LHSIsShared = isPointerToShared(E->getLHS()->getType());
	bool RHSIsShared = isPointerToShared(E->getRHS()->getType());
	if(LHSIsShared && RHSIsShared && E->getOpcode() == BO_Sub) {
	  // Pointer - Pointer
	  QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	  int ElementSize = SemaRef.Context.getTypeSizeInChars(PointeeType).getQuantity();
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(TransformExpr(RHS).get());
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	  int LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	  if(LayoutQualifier == 0) {
	    return BuildUPCRCall(Decls->UPCR_SUB_PSHAREDI, args);
	  } else if(LayoutQualifier == 1) {
	    return BuildUPCRCall(Decls->UPCR_SUB_PSHARED1, args);
	  } else {
	    args.push_back(CreateInteger(SemaRef.Context.getSizeType(), LayoutQualifier));
	    return BuildUPCRCall(Decls->UPCR_SUB_SHARED, args);
	  }
	} else if((LHSIsShared || RHSIsShared) && (E->getOpcode() == BO_Add || E->getOpcode() == BO_Sub)) {
	  // Pointer +/- Integer
	  if(RHSIsShared) { std::swap(LHS, RHS); }
	  QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	  int ElementSize = SemaRef.Context.getTypeSizeInChars(PointeeType).getQuantity();
	  Expr *IntVal = TransformExpr(RHS).get();
	  if(E->getOpcode() == BO_Sub) {
	    IntVal = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Minus, IntVal).get();
	  }
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	  args.push_back(IntVal);
	  int LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	  if(LayoutQualifier == 0) {
	    return BuildUPCRCall(Decls->UPCR_ADD_PSHAREDI, args);
	  } else if(LayoutQualifier == 1) {
	    return BuildUPCRCall(Decls->UPCR_ADD_PSHARED1, args);
	  } else {
	    args.push_back(CreateInteger(SemaRef.Context.getSizeType(), LayoutQualifier));
	    return BuildUPCRCall(Decls->UPCR_ADD_SHARED, args);
	  }
	} else if(LHSIsShared && RHSIsShared && (E->getOpcode() == BO_EQ || E->getOpcode() == BO_NE)) {
	  // Equality Comparison
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(TransformExpr(RHS).get());
	  QualType LHSPointee = LHS->getType()->getAs<PointerType>()->getPointeeType();
	  QualType RHSPointee = RHS->getType()->getAs<PointerType>()->getPointeeType();
	  ExprResult Result;
	  if(isPhaseless(LHSPointee) && isPhaseless(RHSPointee)) {
	    Result = BuildUPCRCall(Decls->UPCR_ISEQUAL_PSHARED_PSHARED, args);
	  } else if(isPhaseless(LHSPointee) && !isPhaseless(RHSPointee)) {
	    Result = BuildUPCRCall(Decls->UPCR_ISEQUAL_PSHARED_SHARED, args);
	  } else if(!isPhaseless(LHSPointee) && isPhaseless(RHSPointee)) {
	    Result = BuildUPCRCall(Decls->UPCR_ISEQUAL_SHARED_PSHARED, args);
	  } else if(!isPhaseless(LHSPointee) && !isPhaseless(RHSPointee)) {
	    Result = BuildUPCRCall(Decls->UPCR_ISEQUAL_SHARED_SHARED, args);
	  }
	  if(E->getOpcode() == BO_NE) {
	    Result = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_LNot, Result.get());
	  }
	  return Result;
	} else if(LHSIsShared && RHSIsShared && (E->getOpcode() == BO_LT || E->getOpcode() == BO_LE || E->getOpcode() == BO_GT || E->getOpcode() == BO_GE)) {
	  // Relational Comparison
	  QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	  int ElementSize = SemaRef.Context.getTypeSizeInChars(PointeeType).getQuantity();
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(TransformExpr(RHS).get());
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	  int LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	  Expr *Diff;
	  if(LayoutQualifier == 0) {
	    Diff = BuildUPCRCall(Decls->UPCR_SUB_PSHAREDI, args).get();
	  } else if(LayoutQualifier == 1) {
	    Diff = BuildUPCRCall(Decls->UPCR_SUB_PSHARED1, args).get();
	  } else {
	    args.push_back(CreateInteger(SemaRef.Context.getSizeType(), LayoutQualifier));
	    Diff = BuildUPCRCall(Decls->UPCR_SUB_SHARED, args).get();
	  }
	  return SemaRef.CreateBuiltinBinOp(SourceLocation(), E->getOpcode(), Diff, CreateInteger(SemaRef.Context.IntTy, 0));
	}
      }
      // Otherwise use the default transform
      return TreeTransform::TransformBinaryOperator(E);
    }
    ExprResult TransformCompoundAssignOperator(CompoundAssignOperator *E) {
      if(E->getLHS()->getType().getQualifiers().hasShared()) {
	QualType Ty = E->getLHS()->getType();
	bool Phaseless = isPhaseless(Ty);
	QualType PtrType = Phaseless? Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	VarDecl * TmpPtrDecl = CreateTmpVar(PtrType);
	BinaryOperatorKind Opc = BinaryOperator::getOpForCompoundAssignment(E->getOpcode());
	Expr * TmpPtr = SemaRef.BuildDeclRefExpr(TmpPtrDecl, PtrType, VK_LValue, SourceLocation()).get();
	Expr * SaveLHS = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr, BuildParens(TransformExpr(E->getLHS()).get()).get()).get();
	Expr * RHS = BuildParens(TransformExpr(E->getRHS()).get()).get();
	Expr * LHSVal = BuildUPCRLoad(TmpPtr, TransformType(Ty.getUnqualifiedType()), Ty).get();
	Expr * OpResult = SemaRef.CreateBuiltinBinOp(SourceLocation(), Opc, LHSVal, RHS).get();
	Expr * Result = BuildUPCRStore(TmpPtr, OpResult, Ty).get();
	return BuildParens(BuildComma(SaveLHS, Result).get());
      } else {
	return TreeTransform::TransformCompoundAssignOperator(E);
      }
    }
    ExprResult TransformArraySubscriptExpr(ArraySubscriptExpr *E) {
      if(isPointerToShared(E->getBase()->getType())) {
	Expr *LHS = E->getBase();
	Expr *RHS = E->getIdx();
	QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	int ElementSize = SemaRef.Context.getTypeSizeInChars(PointeeType).getQuantity();
	Expr *IntVal = TransformExpr(RHS).get();
	std::vector<Expr*> args;
	args.push_back(TransformExpr(LHS).get());
	args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	args.push_back(IntVal);
	int LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	if(LayoutQualifier == 0) {
	  return BuildUPCRCall(Decls->UPCR_ADD_PSHAREDI, args);
	} else if(LayoutQualifier == 1) {
	  return BuildUPCRCall(Decls->UPCR_ADD_PSHARED1, args);
	} else {
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), LayoutQualifier));
	  return BuildUPCRCall(Decls->UPCR_ADD_SHARED, args);
	}
      } else {
	return TreeTransform::TransformArraySubscriptExpr(E);
      }
    }
    StmtResult TransformUPCForAllStmt(UPCForAllStmt *S) {
      // Transform the initialization statement
      StmtResult Init = getDerived().TransformStmt(S->getInit());

      // Transform the condition
      ExprResult Cond;
      VarDecl *ConditionVar = 0;
      if (S->getConditionVariable()) {
	ConditionVar
        = cast_or_null<VarDecl>(
                     TransformDefinition(
                                        S->getConditionVariable()->getLocation(),
                                                      S->getConditionVariable()));
      } else {
	Cond = TransformExpr(S->getCond());
	
	if (S->getCond()) {
	  // Convert the condition to a boolean value.
	  ExprResult CondE = getSema().ActOnBooleanCondition(0, S->getForLoc(),
							     Cond.get());
	  
	  Cond = CondE.get();
	}
      }
      
      Sema::FullExprArg FullCond(getSema().MakeFullExpr(Cond.take()));
      
      // Transform the increment
      ExprResult Inc = TransformExpr(S->getInc());
      if (Inc.isInvalid())
	return StmtError();
      
      Sema::FullExprArg FullInc(getSema().MakeFullExpr(Inc.get()));

      // Transform the body
      StmtResult Body = TransformStmt(S->getBody());

      StmtResult PlainFor = SemaRef.ActOnForStmt(S->getForLoc(), S->getLParenLoc(),
						 Init.get(), FullCond, ConditionVar,
						 FullInc, S->getRParenLoc(), Body.get());

      // If the thread affinity is not specified, upc_forall is
      // the same as a for loop.
      if(!S->getAfnty()) {
	return PlainFor;
      }

      ExprResult Afnty = TransformExpr(S->getAfnty());
      ExprResult ThreadTest;
      if(isPointerToShared(S->getAfnty()->getType())) {
	bool Phaseless = isPhaseless(S->getAfnty()->getType()->getAs<PointerType>()->getPointeeType());
	std::vector<Expr*> args;
	args.push_back(Afnty.get());
	ThreadTest = BuildUPCRCall(Phaseless?Decls->upcr_hasMyAffinity_pshared:Decls->upcr_hasMyAffinity_shared, args);
      } else {
	std::vector<Expr*> args;
	ThreadTest = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_EQ, Afnty.get(), BuildUPCRCall(Decls->upcr_mythread, args).get());
      }

      StmtResult UPCBody = SemaRef.ActOnIfStmt(SourceLocation(), SemaRef.MakeFullExpr(ThreadTest.get()), NULL, Body.get(), SourceLocation(), NULL);

      StmtResult UPCFor = SemaRef.ActOnForStmt(S->getForLoc(), S->getLParenLoc(),
						 Init.get(), FullCond, ConditionVar,
						 FullInc, S->getRParenLoc(), UPCBody.get());

      StmtResult UPCForWrapper;
      {
	Sema::CompoundScopeRAII BodyScope(SemaRef);
	SmallVector<Stmt*, 8> Statements;
	Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, BuildUPCRDeclRef(Decls->upcr_forall_control).get(), CreateInteger(SemaRef.Context.IntTy, 1)).get());
	Statements.push_back(UPCFor.get());
	Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, BuildUPCRDeclRef(Decls->upcr_forall_control).get(), CreateInteger(SemaRef.Context.IntTy, 0)).get());

	UPCForWrapper = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
      }

      return SemaRef.ActOnIfStmt(SourceLocation(), SemaRef.MakeFullExpr(BuildUPCRDeclRef(Decls->upcr_forall_control).get()), NULL, PlainFor.get(), SourceLocation(), UPCForWrapper.get());
    }
    VarDecl *CreateTmpVar(QualType Ty) {
      int ID = static_cast<int>(LocalTemps.size());
      std::string name = (llvm::Twine("_bupc_spilld") + llvm::Twine(ID)).str();
      VarDecl *TmpVar = VarDecl::Create(SemaRef.Context, SemaRef.getFunctionLevelDeclContext(), SourceLocation(), SourceLocation(), &SemaRef.Context.Idents.get(name), Ty, SemaRef.Context.getTrivialTypeSourceInfo(Ty), SC_Auto, SC_None);
      LocalTemps.push_back(TmpVar);
      return TmpVar;
    }
    Decl *TransformDecl(SourceLocation Loc, Decl *D) {
      if(D == NULL) return NULL;
      Decl *Result = TreeTransform::TransformDecl(Loc, D);
      if(Result == D) {
	Result = TransformDeclaration(D, SemaRef.CurContext);
	transformedLocalDecl(D, Result);
      }
      return Result;
    }
    //Decl *TransformDefinition(SourceLocation Loc, Decl *D) {
    //  return TransformDeclaration(D, SemaRef.CurContext);
    //}
    Decl *TransformDeclaration(Decl *D, DeclContext *DC) {
      Decl *Result = TransformDeclarationImpl(D, DC);
      transformedLocalDecl(D, Result);
      return Result;
    }
    bool isPhaseless(QualType Pointee) {
      return Pointee.getQualifiers().getLayoutQualifier() <= 1;
    }
    QualType TransformPointerType(TypeLocBuilder &TLB, PointerTypeLoc TL) {
      if(isPointerToShared(TL.getType())) {
	QualType Result = isPhaseless(TL.getType()->getAs<PointerType>()->getPointeeType())?
	  Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	TypedefTypeLoc NewT = TLB.push<TypedefTypeLoc>(Result);
	NewT.setNameLoc(SourceLocation());
	return Result;
      } else {
	return TreeTransform::TransformPointerType(TLB, TL);
      }
    }
    Decl *TransformDeclarationImpl(Decl *D, DeclContext *DC) {
      if(TranslationUnitDecl *TUD = dyn_cast<TranslationUnitDecl>(D)) {
	return TransformTranslationUnitDecl(TUD);
      } else if(FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
	TypeSourceInfo * FTSI = FD->getTypeSourceInfo()? TransformType(FD->getTypeSourceInfo()) : 0;
	FunctionDecl *result = FunctionDecl::Create(SemaRef.Context, DC, FD->getLocStart(),
				    FD->getNameInfo(), TransformType(FD->getType()),
				    FTSI,
				    FD->getStorageClass(), FD->getStorageClassAsWritten(),
				    FD->isInlineSpecified(), FD->hasWrittenPrototype(),
				    FD->isConstexpr());
	transformedLocalDecl(D, result);
	// Copy the parameters
	SmallVector<ParmVarDecl *, 2> Parms;
	int i = 0;
	for(FunctionDecl::param_iterator iter = FD->param_begin(), end = FD->param_end(); iter != end; ++iter) {
	  ParmVarDecl *OldParam = *iter;
	  TypeSourceInfo *PTSI = OldParam->getTypeSourceInfo()?TransformType(OldParam->getTypeSourceInfo()):0;
	  ParmVarDecl *Param = ParmVarDecl::Create(SemaRef.Context, result, OldParam->getLocStart(),
						   OldParam->getLocation(), OldParam->getIdentifier(),
						   TransformType(OldParam->getType()),
						   PTSI,
						   OldParam->getStorageClass(),
						   OldParam->getStorageClassAsWritten(),
						   TransformExpr(OldParam->getDefaultArg()).get());
	  Param->setScopeInfo(0, i++);
	  Parms.push_back(Param);
	}
	result->setParams(Parms);

	if(FD->doesThisDeclarationHaveABody()) {
	  SemaRef.ActOnStartOfFunctionDef(0, result);
	  Sema::SynthesizedFunctionScope Scope(SemaRef, result);
	  Stmt *UserBody = TransformStmt(FD->getBody()).get();
	  llvm::SmallVector<Stmt*, 8> Body;
	  {
	    std::vector<Expr*> args;
	    Body.push_back(BuildUPCRCall(Decls->UPCR_BEGIN_FUNCTION, args).get());
	  }
	  // Insert all the temporary variables that we created
	  for(std::vector<VarDecl*>::const_iterator iter = LocalTemps.begin(), end = LocalTemps.end(); iter != end; ++iter) {
	    Decl *decl_arr[] = { *iter };
	    Body.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, decl_arr, 1)), SourceLocation(), SourceLocation()).get());
	  }
	  LocalTemps.clear();
	  // Insert the user code
	  Body.push_back(UserBody);
	  SemaRef.ActOnFinishFunctionBody(result, SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Body, false).get());
	}
	return result;
      } else if(VarDecl *VD = dyn_cast<VarDecl>(D)) {
	if(VD->getType().getQualifiers().hasShared()) {
	  QualType VarType = (isPhaseless(VD->getType())? Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t );
	  VarDecl *result = VarDecl::Create(SemaRef.Context, DC, VD->getLocStart(),
					    VD->getLocation(), VD->getIdentifier(),
					    VarType, SemaRef.Context.getTrivialTypeSourceInfo(VarType), VD->getStorageClass(), VD->getStorageClassAsWritten());
	  SharedGlobals.push_back(std::make_pair(result, VD));
	  if(Expr *Init = VD->getInit()) {
	    SharedInitializers.push_back(std::make_pair(result, TransformExpr(Init).get()));
	  }
	  return result;
	} else {
	  VarDecl *result = VarDecl::Create(SemaRef.Context, DC, VD->getLocStart(), VD->getLocation(), VD->getIdentifier(),
					    TransformType(VD->getType()), TransformType(VD->getTypeSourceInfo()),
					    VD->getStorageClass(), VD->getStorageClassAsWritten());
	  if(Expr *Init = VD->getInit()) {
	    result->setInit(TransformExpr(Init).get());
	  }
	  return result;
	}
      } else if(RecordDecl *RD = dyn_cast<RecordDecl>(D)) {
	RecordDecl *Result = RecordDecl::Create(SemaRef.Context, RD->getTagKind(), DC,
				  RD->getLocStart(), RD->getLocation(),
				  RD->getIdentifier(), cast_or_null<RecordDecl>(TransformDecl(SourceLocation(), RD->getPreviousDecl())));
	transformedLocalDecl(D, Result);
	SmallVector<Decl *, 4> Fields;
	if(RD->isThisDeclarationADefinition()) {
	  Result->startDefinition();
	  for(RecordDecl::decl_iterator iter = RD->decls_begin(), end = RD->decls_end(); iter != end; ++iter) {
	    if(FieldDecl *FD = dyn_cast_or_null<FieldDecl>(*iter)) {
	      TypeSourceInfo *DI = FD->getTypeSourceInfo();
	      if(DI) DI = TransformType(DI);
	      FieldDecl *NewFD = SemaRef.CheckFieldDecl(FD->getDeclName(), TransformType(FD->getType()), DI, Result, FD->getLocation(), FD->isMutable(), TransformExpr(FD->getBitWidth()).get(), FD->getInClassInitStyle(), FD->getInnerLocStart(), FD->getAccess(), 0);
	      
	      NewFD->setImplicit(FD->isImplicit());
	      NewFD->setAccess(FD->getAccess());
	      Result->addDecl(NewFD);
	      Fields.push_back(NewFD);
	    }
	  }
	  SemaRef.ActOnFields(0, Result->getLocation(), Result, Fields, SourceLocation(), SourceLocation(), 0);
	}
	return Result;
      } else if(TypedefDecl *TD = dyn_cast<TypedefDecl>(D)) {
	return TypedefDecl::Create(SemaRef.Context, DC, TD->getLocStart(), TD->getLocation(), TD->getIdentifier(), TransformType(TD->getTypeSourceInfo()));
      } else if(EnumDecl *ED = dyn_cast<EnumDecl>(D)) {
	EnumDecl * PrevDecl = 0;
	if(EnumDecl * OrigPrevDecl = ED->getPreviousDecl()) {
	  PrevDecl = cast<EnumDecl>(TransformDecl(SourceLocation(), OrigPrevDecl));
	}

	EnumDecl *Result = EnumDecl::Create(SemaRef.Context, DC, ED->getLocStart(), ED->getLocation(),
					    ED->getIdentifier(), PrevDecl, ED->isScoped(),
					    ED->isScopedUsingClassTag(), ED->isFixed());
	transformedLocalDecl(D, Result);
	Result->startDefinition();

	SmallVector<Decl *, 4> Enumerators;

	EnumConstantDecl *PrevEnumConstant = 0;
	for(EnumDecl::enumerator_iterator iter = ED->enumerator_begin(), end = ED->enumerator_end(); iter != end; ++iter) {
	  Expr *Value = 0;
	  if(Expr *OrigValue = iter->getInitExpr()) {
	    Value = TransformExpr(OrigValue).get();
	  }
	  EnumConstantDecl *EnumConstant = SemaRef.CheckEnumConstant(Result, PrevEnumConstant, iter->getLocation(), iter->getIdentifier(), Value);

	  EnumConstant->setAccess(Result->getAccess());
	  Result->addDecl(EnumConstant);
	  Enumerators.push_back(EnumConstant);
	  PrevEnumConstant = EnumConstant;

	}

	SemaRef.ActOnEnumBody(Result->getLocation(), SourceLocation(), Result->getRBraceLoc(), Result, Enumerators.data(), Enumerators.size(), 0, 0);
	return Result;
      } else {
	assert(!"Unknown Decl");
      }
    }
    Decl *TransformTranslationUnitDecl(TranslationUnitDecl *D) {
      TranslationUnitDecl *result = SemaRef.Context.getTranslationUnitDecl();
      Scope CurScope(0, Scope::DeclScope, SemaRef.getDiagnostics());
      SemaRef.setCurScope(&CurScope);
      SemaRef.PushDeclContext(&CurScope, result);
      CopyDeclContext(D, result);
      if(FunctionDecl *Alloc = GetSharedAllocationFunction()) {
	result->addDecl(Alloc);
      }
      if(FunctionDecl *Init = GetSharedInitializationFunction()) {
	result->addDecl(Init);
      }
      SemaRef.setCurScope(0);
      return result;
    }
    UPCRDecls *Decls;
    void CopyDeclContext(DeclContext *Src, DeclContext *Dst) {
      for(DeclContext::decl_iterator iter = Src->decls_begin(),
          end = Src->decls_end(); iter != end; ++iter) {
	Dst->addDecl(TransformDeclaration(*iter, Dst));
      }
    }
    std::vector<VarDecl*> LocalTemps;
    // The shared variables that need to be initialized
    // all must have type upcr_shared_ptr_t
    // first = upcr_shared_ptr_t, second = original declaration
    // This must be called at the end of the transformation
    // after all variables with static storage duration
    // have been processed
    typedef std::vector<std::pair<VarDecl*, VarDecl*> > SharedGlobalsType;
    std::vector<std::pair<VarDecl*, VarDecl*> > SharedGlobals;
    FunctionDecl* GetSharedAllocationFunction() {
      // FIXME: randomize (?) the name
      FunctionDecl *Result = Decls->CreateFunction(SemaRef.Context, "UPCRI_ALLOC_test", SemaRef.Context.VoidTy, 0, 0);
      SemaRef.ActOnStartOfFunctionDef(0, Result);
      Sema::SynthesizedFunctionScope Scope(SemaRef, Result);
      StmtResult Body;
      {
	Sema::CompoundScopeRAII BodyScope(SemaRef);
	SmallVector<Stmt*, 8> Statements;
	{
	  std::vector<Expr*> args;
	  Statements.push_back(BuildUPCRCall(Decls->UPCR_BEGIN_FUNCTION, args).get());
	}
	int SizeTypeSize = SemaRef.Context.getTypeSize(SemaRef.Context.getSizeType());
	QualType _bupc_info_type = SemaRef.Context.getIncompleteArrayType(Decls->upcr_startup_shalloc_t, ArrayType::Normal, 0);
	QualType _bupc_pinfo_type = SemaRef.Context.getIncompleteArrayType(Decls->upcr_startup_pshalloc_t, ArrayType::Normal, 0);
	SmallVector<Expr*, 8> Initializers;
	SmallVector<Expr*, 8> PInitializers;
	for(SharedGlobalsType::const_iterator iter = SharedGlobals.begin(), end = SharedGlobals.end();
	    iter != end; ++iter) {
	  std::vector<Expr*> args;
	  bool Phaseless = (iter->first->getType() == Decls->upcr_pshared_ptr_t);
	  args.push_back(SemaRef.BuildDeclRefExpr(iter->first, iter->first->getType(), VK_LValue, SourceLocation()).get());
	  int LayoutQualifier = iter->second->getType().getQualifiers().getLayoutQualifier();
	  llvm::APInt ArrayDimension(SizeTypeSize, 1);
	  bool hasThread = false;
	  QualType ElemTy = iter->second->getType().getCanonicalType();
	  while(const ArrayType *AT = dyn_cast<ArrayType>(ElemTy.getTypePtr())) {
	    if(const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(AT)) {
	      ArrayDimension *= CAT->getSize();
	    } else if(const UPCThreadArrayType *TAT = dyn_cast<UPCThreadArrayType>(AT)) {
	      if(TAT->getThread()) {
		hasThread = true;
	      }
	      ArrayDimension *= TAT->getSize();
	    } else {
	      assert(!"Other array types should not syntax check");
	    }
	    ElemTy = AT->getElementType();
	  }
	  int ElementSize = SemaRef.Context.getTypeSizeInChars(ElemTy).getQuantity();
	  if(LayoutQualifier == 0) {
	    // FIXME:
	  } else {
	    args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, LayoutQualifier * ElementSize), SemaRef.Context.getSizeType(), SourceLocation()));
	    args.push_back(IntegerLiteral::Create(SemaRef.Context, (ArrayDimension + LayoutQualifier - 1).udiv(llvm::APInt(SizeTypeSize, LayoutQualifier)), SemaRef.Context.getSizeType(), SourceLocation()));
	    args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, hasThread), SemaRef.Context.getSizeType(), SourceLocation()));
	    args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, ElementSize), SemaRef.Context.getSizeType(), SourceLocation()));
	    // FIXME: encode the correct mangled type
	    args.push_back(StringLiteral::Create(SemaRef.Context, "", StringLiteral::Ascii, false, SemaRef.Context.getPointerType(SemaRef.Context.getConstType(SemaRef.Context.CharTy)), SourceLocation()));
	    if(Phaseless) {
	      PInitializers.push_back(BuildUPCRCall(Decls->UPCRT_STARTUP_PSHALLOC, args).get());
	    } else {
	      Initializers.push_back(BuildUPCRCall(Decls->UPCRT_STARTUP_SHALLOC, args).get());
	    }
	  }
	}
	VarDecl *_bupc_info;
	VarDecl *_bupc_pinfo;
	if(!Initializers.empty()) {
	  _bupc_info = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(),
						 &SemaRef.Context.Idents.get("_bupc_info"), _bupc_info_type, SemaRef.Context.getTrivialTypeSourceInfo(_bupc_info_type), SC_Auto, SC_None);
	  // InitializerList semantics vary depending on whether the SourceLocations are valid.
	  SemaRef.AddInitializerToDecl(_bupc_info, SemaRef.ActOnInitList(Decls->FakeLocation, Initializers, Decls->FakeLocation).get(), false, false);
	  Decl *_bupc_info_arr[] = { _bupc_info };
	  Statements.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, _bupc_info_arr, 1)), SourceLocation(), SourceLocation()).get());
	}
	if(!PInitializers.empty()) {
	  _bupc_pinfo = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(),
						 &SemaRef.Context.Idents.get("_bupc_pinfo"), _bupc_pinfo_type, SemaRef.Context.getTrivialTypeSourceInfo(_bupc_pinfo_type), SC_Auto, SC_None);
	  // InitializerList semantics vary depending on whether the SourceLocations are valid.
	  SemaRef.AddInitializerToDecl(_bupc_pinfo, SemaRef.ActOnInitList(Decls->FakeLocation, PInitializers, Decls->FakeLocation).get(), false, false);
	  Decl *_bupc_pinfo_arr[] = { _bupc_pinfo };
	  Statements.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, _bupc_pinfo_arr, 1)), SourceLocation(), SourceLocation()).get());
	}
	if(!Initializers.empty()) {
	  std::vector<Expr*> args;
	  args.push_back(SemaRef.BuildDeclRefExpr(_bupc_info, _bupc_info_type, VK_LValue, SourceLocation()).get());
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, Initializers.size()), SemaRef.Context.getSizeType(), SourceLocation()));
	  Statements.push_back(BuildUPCRCall(Decls->upcr_startup_shalloc, args).get());
	}
	if(!PInitializers.empty()) {
	  std::vector<Expr*> args;
	  args.push_back(SemaRef.BuildDeclRefExpr(_bupc_pinfo, _bupc_pinfo_type, VK_LValue, SourceLocation()).get());
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, PInitializers.size()), SemaRef.Context.getSizeType(), SourceLocation()));
	  Statements.push_back(BuildUPCRCall(Decls->upcr_startup_pshalloc, args).get());
	}
	Body = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
      }
      SemaRef.ActOnFinishFunctionBody(Result, Body.get());
      return Result;
    }

    Stmt *CreateSimpleDeclStmt(Decl * D) {
      Decl *Decls[] = { D };
      return SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, Decls, 1)), SourceLocation(), SourceLocation()).get();
    }

    typedef std::vector<std::pair<VarDecl *, Expr *> > SharedInitializersType;
    SharedInitializersType SharedInitializers;
    FunctionDecl * GetSharedInitializationFunction() {
      // FIXME: randomize (?) the name
      FunctionDecl *Result = Decls->CreateFunction(SemaRef.Context, "UPCRI_INIT_test", SemaRef.Context.VoidTy, 0, 0);
      SemaRef.ActOnStartOfFunctionDef(0, Result);
      Sema::SynthesizedFunctionScope Scope(SemaRef, Result);
      StmtResult Body;
      {
	Sema::CompoundScopeRAII BodyScope(SemaRef);
	SmallVector<Stmt*, 8> Statements;
	{
	  std::vector<Expr*> args;
	  Statements.push_back(BuildUPCRCall(Decls->UPCR_BEGIN_FUNCTION, args).get());
	}
	
	Expr *Cond;
	{
	  std::vector<Expr*> args;
	  Expr *mythread = BuildUPCRCall(Decls->upcr_mythread, args).get();
	  Cond = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_EQ, mythread, CreateInteger(SemaRef.Context.IntTy, 0)).get();
	}

	std::vector<VarDecl *> Initializers;
	for(SharedInitializersType::iterator iter = SharedInitializers.begin(), end = SharedInitializers.end(); iter != end; ++iter) {
	  std::string VarName = (Twine("_bupc_") + iter->first->getIdentifier()->getName() + "_val").str();
	  VarDecl *StoredInit = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(), &SemaRef.Context.Idents.get(VarName),
						iter->second->getType(), SemaRef.Context.getTrivialTypeSourceInfo(iter->second->getType()),
						SC_Auto, SC_None);
	  StoredInit->setInit(iter->second);
	  Initializers.push_back(StoredInit);
	  Statements.push_back(CreateSimpleDeclStmt(StoredInit));
	}
	
	{
	  SmallVector<Stmt*, 8> PutOnce;
	  for(std::size_t i = 0; i < SharedInitializers.size(); ++i) {
	    std::vector<Expr*> args;
	    args.push_back(CreateSimpleDeclRef(SharedInitializers[i].first));
	    args.push_back(CreateInteger(SemaRef.Context.IntTy, 0));
	    args.push_back(SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, CreateSimpleDeclRef(Initializers[i])).get());
	    args.push_back(CreateInteger(SemaRef.Context.IntTy, SemaRef.Context.getTypeSizeInChars(Initializers[i]->getType()).getQuantity()));
	    bool Phaseless = SharedInitializers[i].first->getType() == Decls->upcr_pshared_ptr_t;
	    PutOnce.push_back(BuildUPCRCall(Phaseless?Decls->upcr_put_pshared:Decls->upcr_put_shared, args).get());
	  }
	  Statements.push_back(SemaRef.ActOnIfStmt(SourceLocation(), SemaRef.MakeFullExpr(Cond), NULL, SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), PutOnce, false).get(), SourceLocation(), NULL).get());
	}

	Body = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
      }
      SemaRef.ActOnFinishFunctionBody(Result, Body.get());
      return Result;
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
  options.push_back("-fsyntax-only");
  FileManager Files((FileSystemOptions()));
  ToolInvocation tool(options, new RemoveUPCAction, &Files);
  tool.run();
}
