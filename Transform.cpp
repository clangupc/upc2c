#include <clang/Tooling/Tooling.h>
#include <clang/Sema/SemaConsumer.h>
#include <clang/Sema/Scope.h>
#include <clang/Lex/HeaderSearch.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Frontend/FrontendAction.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Tooling/CommonOptionsParser.h>
#include <llvm/Option/OptTable.h>
#include <llvm/Option/ArgList.h>
#include <llvm/Option/Arg.h>
#include <clang/Driver/Options.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/FileSystem.h>
#include <string>
#include <cctype>
#include <memory>
#include "../../lib/Sema/TreeTransform.h"

#include <clang/AST/PrettyPrinter.h>

using namespace clang;
using namespace clang::tooling;
using llvm::APInt;

namespace {

  struct is_ident_char {
    typedef bool result_type;
    typedef char argument_type;
    bool operator()(char arg) const {
      return std::isalnum(arg) || arg == '_';
    }
  };

  std::string get_file_id(const std::string& filename) {
    uint32_t seed = 0;
    for(std::string::const_iterator iter = filename.begin(), end = filename.end(); iter != end; ++iter) {
      seed ^= uint32_t(*iter) + 0x9e3779b9 + (seed<<6) + (seed>>2);
    }
    std::string as_identifier(llvm::sys::path::stem(filename));
    std::replace_if(as_identifier.begin(), as_identifier.end(), std::not1(is_ident_char()), '_');
    return (as_identifier + "_" + llvm::Twine(seed)).str();
  }

  /* Copied from DeclPrinter.cpp */
  static QualType GetBaseType(QualType T) {
    // FIXME: This should be on the Type class!
    QualType BaseType = T;
    while (!BaseType->isSpecifierType()) {
      if (isa<TypedefType>(BaseType))
	break;
      else if (const PointerType* PTy = BaseType->getAs<PointerType>())
	BaseType = PTy->getPointeeType();
      else if (const BlockPointerType *BPy = BaseType->getAs<BlockPointerType>())
	BaseType = BPy->getPointeeType();
      else if (const ArrayType* ATy = dyn_cast<ArrayType>(BaseType))
	BaseType = ATy->getElementType();
      else if (const FunctionType* FTy = BaseType->getAs<FunctionType>())
	BaseType = FTy->getReturnType();
      else if (const VectorType *VTy = BaseType->getAs<VectorType>())
	BaseType = VTy->getElementType();
      else if (const ReferenceType *RTy = BaseType->getAs<ReferenceType>())
	BaseType = RTy->getPointeeType();
      else
	llvm_unreachable("Unknown declarator!");
    }
    return BaseType;
  }

  static QualType getDeclType(Decl* D) {
    if (TypedefNameDecl* TDD = dyn_cast<TypedefNameDecl>(D))
      return TDD->getUnderlyingType();
    if (ValueDecl* VD = dyn_cast<ValueDecl>(D))
      return VD->getType();
    return QualType();
  }

  typedef enum {
    CFNK_PSHARED = 0,
    CFNK_PSHARED_STRICT,
    CFNK_SHARED,
    CFNK_SHARED_STRICT
  } UPCRCommGroupKind;
  struct UPCRCommFn {
  private:
    FunctionDecl* Decls[4];
  public:
    UPCRCommFn() : Decls() {}
    FunctionDecl*& operator[](int idx) {
      return Decls[idx];
    }
    FunctionDecl*& operator()(bool Phaseless, bool Strict = false) {
      return Decls[Phaseless? (Strict? CFNK_PSHARED_STRICT : CFNK_PSHARED)
                            : (Strict? CFNK_SHARED_STRICT  : CFNK_SHARED)];
    }
  };


  struct UPCRDecls {
    FunctionDecl * upcr_notify;
    FunctionDecl * upcr_wait;
    FunctionDecl * upcr_barrier;
    FunctionDecl * upcr_poll;
    FunctionDecl * upcr_mythread;
    FunctionDecl * upcr_threads;
    FunctionDecl * upcr_hasMyAffinity_pshared;
    FunctionDecl * upcr_hasMyAffinity_shared;
    FunctionDecl * UPCR_BEGIN_FUNCTION;
    FunctionDecl * UPCR_EXIT_FUNCTION;
    FunctionDecl * UPCRT_STARTUP_PSHALLOC;
    FunctionDecl * UPCRT_STARTUP_SHALLOC;
    FunctionDecl * upcr_startup_pshalloc;
    FunctionDecl * upcr_startup_shalloc;
    FunctionDecl * UPCR_TLD_ADDR;
    FunctionDecl * UPCR_ADD_SHARED;
    FunctionDecl * UPCR_ADD_PSHAREDI;
    FunctionDecl * UPCR_ADD_PSHARED1;
    FunctionDecl * UPCR_INC_SHARED;
    FunctionDecl * UPCR_INC_PSHAREDI;
    FunctionDecl * UPCR_INC_PSHARED1;
    FunctionDecl * UPCR_SUB_SHARED;
    FunctionDecl * UPCR_SUB_PSHAREDI;
    FunctionDecl * UPCR_SUB_PSHARED1;
    FunctionDecl * UPCR_ISEQUAL_SHARED_SHARED;
    FunctionDecl * UPCR_ISEQUAL_SHARED_PSHARED;
    FunctionDecl * UPCR_ISEQUAL_PSHARED_SHARED;
    FunctionDecl * UPCR_ISEQUAL_PSHARED_PSHARED;
    FunctionDecl * UPCR_PSHARED_TO_LOCAL;
    FunctionDecl * UPCR_SHARED_TO_LOCAL;
    FunctionDecl * UPCR_ISNULL_PSHARED;
    FunctionDecl * UPCR_ISNULL_SHARED;
    FunctionDecl * UPCR_SHARED_TO_PSHARED;
    FunctionDecl * UPCR_PSHARED_TO_SHARED;
    FunctionDecl * UPCR_SHARED_RESETPHASE;
    FunctionDecl * UPCR_ADDRFIELD_SHARED;
    FunctionDecl * UPCR_ADDRFIELD_PSHARED;
    UPCRCommFn UPCR_GET;
    UPCRCommFn UPCR_GET_IVAL;
    UPCRCommFn UPCR_GET_FVAL;
    UPCRCommFn UPCR_GET_DVAL;
    UPCRCommFn UPCR_PUT;
    UPCRCommFn UPCR_PUT_IVAL;
    UPCRCommFn UPCR_PUT_FVAL;
    UPCRCommFn UPCR_PUT_DVAL;
    VarDecl * upcrt_forall_control;
    VarDecl * upcr_null_shared;
    VarDecl * upcr_null_pshared;
    QualType upcr_shared_ptr_t;
    QualType upcr_pshared_ptr_t;
    QualType upcr_startup_shalloc_t;
    QualType upcr_startup_pshalloc_t;
    QualType upcr_register_value_t;
    SourceLocation FakeLocation;
    explicit UPCRDecls(ASTContext& Context) {
      SourceManager& SourceMgr = Context.getSourceManager();
      FakeLocation = SourceMgr.getLocForStartOfFile(SourceMgr.getMainFileID());

      // types

      // Make sure that the size and alignment are correct.
      QualType SharedPtrTy = Context.getPointerType(Context.getSharedType(Context.VoidTy));
      upcr_shared_ptr_t = CreateTypedefType(Context, "upcr_shared_ptr_t", SharedPtrTy);
      upcr_pshared_ptr_t = CreateTypedefType(Context, "upcr_pshared_ptr_t", SharedPtrTy);
      upcr_startup_shalloc_t = CreateTypedefType(Context, "upcr_startup_shalloc_t");
      upcr_startup_pshalloc_t = CreateTypedefType(Context, "upcr_startup_pshalloc_t");

      // FIXME: This is a fair assumption, but should really get true type
      upcr_register_value_t = CreateTypedefType(Context, "upcr_register_value_t", Context.getUIntPtrType());

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
      // upcr_poll
      {
	upcr_poll = CreateFunction(Context, "upcr_poll", Context.VoidTy, 0, 0);
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
      // UPCR_ADD_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.IntTy, Context.IntTy };
	UPCR_ADD_SHARED = CreateFunction(Context, "upcr_add_shared", upcr_shared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADD_PSHAREDI
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_ADD_PSHAREDI = CreateFunction(Context, "upcr_add_psharedI", upcr_pshared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADD_PSHARED1
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_ADD_PSHARED1 = CreateFunction(Context, "upcr_add_pshared1", upcr_pshared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_INC_SHARED
      {
	QualType argTypes[] = { Context.getPointerType(upcr_shared_ptr_t), Context.IntTy, Context.IntTy, Context.IntTy };
	UPCR_INC_SHARED = CreateFunction(Context, "upcr_inc_shared", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_INC_PSHAREDI
      {
	QualType argTypes[] = { Context.getPointerType(upcr_pshared_ptr_t), Context.IntTy, Context.IntTy };
	UPCR_INC_PSHAREDI = CreateFunction(Context, "upcr_inc_psharedI", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_INC_PSHARED1
      {
	QualType argTypes[] = { Context.getPointerType(upcr_pshared_ptr_t), Context.IntTy, Context.IntTy };
	UPCR_INC_PSHARED1 = CreateFunction(Context, "upcr_inc_pshared1", Context.VoidTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_SUB_SHARED = CreateFunction(Context, "upcr_sub_shared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_PSHAREDI
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t, Context.IntTy };
	UPCR_SUB_PSHAREDI = CreateFunction(Context, "upcr_sub_psharedI", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SUB_PSHARED1
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t, Context.IntTy };
	UPCR_SUB_PSHARED1 = CreateFunction(Context, "upcr_sub_pshared1", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_SHARED_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_shared_ptr_t };
	UPCR_ISEQUAL_SHARED_SHARED = CreateFunction(Context, "upcr_isequal_shared_shared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_SHARED_PSHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t, upcr_pshared_ptr_t };
	UPCR_ISEQUAL_SHARED_PSHARED = CreateFunction(Context, "upcr_isequal_shared_pshared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_PSHARED_SHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_shared_ptr_t };
	UPCR_ISEQUAL_PSHARED_SHARED = CreateFunction(Context, "upcr_isequal_pshared_shared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISEQUAL_PSHARED_PSHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t, upcr_pshared_ptr_t };
	UPCR_ISEQUAL_PSHARED_PSHARED = CreateFunction(Context, "upcr_isequal_pshared_pshared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SHARED_TO_LOCAL
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	UPCR_SHARED_TO_LOCAL = CreateFunction(Context, "upcr_shared_to_local", Context.VoidPtrTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PSHARED_TO_LOCAL
      {
	QualType argTypes[] = { upcr_pshared_ptr_t };
	UPCR_PSHARED_TO_LOCAL = CreateFunction(Context, "upcr_pshared_to_local", Context.VoidPtrTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISNULL_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	UPCR_ISNULL_SHARED = CreateFunction(Context, "upcr_isnull_shared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ISNULL_PSHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t };
	UPCR_ISNULL_PSHARED = CreateFunction(Context, "upcr_isnull_pshared", Context.IntTy, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SHARED_TO_PSHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	UPCR_SHARED_TO_PSHARED = CreateFunction(Context, "upcr_shared_to_pshared", upcr_pshared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_PSHARED_TO_SHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t };
	UPCR_PSHARED_TO_SHARED = CreateFunction(Context, "upcr_pshared_to_shared", upcr_shared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_SHARED_RESETPHASE
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	UPCR_SHARED_RESETPHASE = CreateFunction(Context, "upcr_shared_resetphase", upcr_shared_ptr_t, argTypes, sizeof(argTypes)/sizeof(argTypes[0]));
      }
      // UPCR_ADDRFIELD_SHARED
      {
	QualType argTypes[] = { upcr_shared_ptr_t };
	UPCR_ADDRFIELD_SHARED = CreateFunction(Context, "upcr_addrfield_shared", Context.getUIntPtrType(), argTypes, 1);
      }
      // UPCR_ADDRFIELD_PSHARED
      {
	QualType argTypes[] = { upcr_pshared_ptr_t };
	UPCR_ADDRFIELD_PSHARED = CreateFunction(Context, "upcr_addrfield_pshared", Context.getUIntPtrType(), argTypes, 1);
      }
      // UPCR_BEGIN_FUNCTION
      {
	UPCR_BEGIN_FUNCTION = CreateFunction(Context, "UPCR_BEGIN_FUNCTION", Context.VoidTy, NULL, 0);
      }
      // UPCR_EXIT_FUNCTION
      {
	UPCR_EXIT_FUNCTION = CreateFunction(Context, "UPCR_EXIT_FUNCTION", Context.VoidTy, NULL, 0);
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
      // UPCR_TLD_ADDR
      {
	UPCR_TLD_ADDR = CreateFunction(Context, "UPCR_TLD_ADDR", Context.VoidPtrTy, NULL, 0, true/*variadic*/);
      }
      // UPCR_GET_{,P}SHARED{,_STRICT}
      {
	QualType pargTypes[] = { Context.VoidPtrTy, upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET[CFNK_PSHARED] = CreateFunction(Context, "upcr_get_pshared", Context.VoidTy, pargTypes, 4);
	UPCR_GET[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_get_pshared_strict", Context.VoidTy, pargTypes, 4);
	QualType argTypes[] = { Context.VoidPtrTy, upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET[CFNK_SHARED] = CreateFunction(Context, "upcr_get_shared", Context.VoidTy, argTypes, 4);
	UPCR_GET[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_get_shared_strict", Context.VoidTy, argTypes, 4);
      }
      // UPCR_GET_{,P}SHARED_IVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_IVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_get_pshared_val", upcr_register_value_t, pargTypes, 3);
	UPCR_GET_IVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_get_pshared_val_strict", upcr_register_value_t, pargTypes, 3);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.IntTy };
	UPCR_GET_IVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_get_shared_val", upcr_register_value_t, argTypes, 3);
	UPCR_GET_IVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_get_shared_val_strict", upcr_register_value_t, argTypes, 3);
      }
      // UPCR_GET_{,P}SHARED_FVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy };
	UPCR_GET_FVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_get_pshared_floatval", Context.FloatTy, pargTypes, 2);
	UPCR_GET_FVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_get_pshared_floatval_strict", Context.FloatTy, pargTypes, 2);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy };
	UPCR_GET_FVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_get_shared_floatval", Context.FloatTy, argTypes, 2);
	UPCR_GET_FVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_get_shared_floatval_strict", Context.FloatTy, argTypes, 2);
      }
      // UPCR_GET_{,P}SHARED_DVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy };
	UPCR_GET_DVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_get_pshared_doubleval", Context.DoubleTy, pargTypes, 2);
	UPCR_GET_DVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_get_pshared_doubleval_strict", Context.DoubleTy, pargTypes, 2);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy };
	UPCR_GET_DVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_get_shared_doubleval", Context.DoubleTy, argTypes, 2);
	UPCR_GET_DVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_get_shared_doubleval_strict", Context.DoubleTy, argTypes, 2);
      }
      // UPCR_PUT_{,P}SHARED{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.VoidPtrTy, Context.IntTy };
	UPCR_PUT[CFNK_PSHARED] = CreateFunction(Context, "upcr_put_pshared", Context.VoidTy, pargTypes, 4);
	UPCR_PUT[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_put_pshared_strict", Context.VoidTy, pargTypes, 4);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.VoidPtrTy, Context.IntTy };
	UPCR_PUT[CFNK_SHARED] = CreateFunction(Context, "upcr_put_shared", Context.VoidTy, argTypes, 4);
	UPCR_PUT[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_put_shared_strict", Context.VoidTy, argTypes, 4);
      }
      // UPCR_PUT_{,P}SHARED_IVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy, upcr_register_value_t, Context.IntTy };
	UPCR_PUT_IVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_put_pshared_val", Context.VoidTy, pargTypes, 4);
	UPCR_PUT_IVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_put_pshared_val_strict", Context.VoidTy, pargTypes, 4);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, upcr_register_value_t, Context.IntTy };
	UPCR_PUT_IVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_put_shared_val", Context.VoidTy, argTypes, 4);
	UPCR_PUT_IVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_put_shared_val_strict", Context.VoidTy, argTypes, 4);
      }
      // UPCR_PUT_{,P}SHARED_FVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.FloatTy };
	UPCR_PUT_FVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_put_pshared_floatval", Context.VoidTy, pargTypes, 3);
	UPCR_PUT_FVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_put_pshared_floatval_strict", Context.VoidTy, pargTypes, 3);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.FloatTy };
	UPCR_PUT_FVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_put_shared_floatval", Context.VoidTy, argTypes, 3);
	UPCR_PUT_FVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_put_shared_floatval_strict", Context.VoidTy, argTypes, 3);
      }
      // UPCR_PUT_{,P}SHARED_DVAL{,_STRICT}
      {
	QualType pargTypes[] = { upcr_pshared_ptr_t, Context.IntTy, Context.DoubleTy };
	UPCR_PUT_DVAL[CFNK_PSHARED] = CreateFunction(Context, "upcr_put_pshared_doubleval", Context.VoidTy, pargTypes, 3);
	UPCR_PUT_DVAL[CFNK_PSHARED_STRICT] = CreateFunction(Context, "upcr_put_pshared_doubleval_strict", Context.VoidTy, pargTypes, 3);
	QualType argTypes[] = { upcr_shared_ptr_t, Context.IntTy, Context.DoubleTy };
	UPCR_PUT_DVAL[CFNK_SHARED] = CreateFunction(Context, "upcr_put_shared_doubleval", Context.VoidTy, argTypes, 3);
	UPCR_PUT_DVAL[CFNK_SHARED_STRICT] = CreateFunction(Context, "upcr_put_shared_doubleval_strict", Context.VoidTy, argTypes, 3);
      }
      // upcrt_forall_control
      {
	DeclContext *DC = Context.getTranslationUnitDecl();
	upcrt_forall_control = VarDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get("upcrt_forall_control"), Context.IntTy, Context.getTrivialTypeSourceInfo(Context.IntTy), SC_Extern);
      }
      // upcr_null_shared
      {
	DeclContext *DC = Context.getTranslationUnitDecl();
	upcr_null_shared = VarDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get("upcr_null_shared"), upcr_shared_ptr_t, Context.getTrivialTypeSourceInfo(upcr_shared_ptr_t), SC_Extern);
      }
      // upcr_null_pshared
      {
	DeclContext *DC = Context.getTranslationUnitDecl();
	upcr_null_pshared = VarDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get("upcr_null_pshared"), upcr_pshared_ptr_t, Context.getTrivialTypeSourceInfo(upcr_pshared_ptr_t), SC_Extern);
      }

    }
    FunctionDecl *CreateFunction(ASTContext& Context, StringRef name, QualType RetType, QualType * argTypes, int numArgs, bool Variadic = false) {
      DeclContext *DC = Context.getTranslationUnitDecl();
      FunctionProtoType::ExtProtoInfo Info;
      if(Variadic) {
        Info.Variadic = true;
      }
      QualType Ty = Context.getFunctionType(RetType, llvm::makeArrayRef(argTypes, numArgs), Info);
      FunctionDecl *Result = FunctionDecl::Create(Context, DC, FakeLocation, FakeLocation, DeclarationName(&Context.Idents.get(name)), Ty, Context.getTrivialTypeSourceInfo(Ty), SC_Extern);
      llvm::SmallVector<ParmVarDecl *, 4> Params;
      for(int i = 0; i < numArgs; ++i) {
	Params.push_back(ParmVarDecl::Create(Context, Result, SourceLocation(), SourceLocation(), 0, argTypes[i], 0, SC_None, 0));
	Params[i]->setScopeInfo(0, i);
      }
      Result->setParams(Params);
      return Result;
    }
    QualType CreateTypedefType(ASTContext& Context, StringRef name) {
      return CreateTypedefType(Context, name, Context.IntTy);
    }
    QualType CreateTypedefType(ASTContext& Context, StringRef name, QualType BaseTy) {
      DeclContext *DC = Context.getTranslationUnitDecl();
      TypedefDecl *Typedef = TypedefDecl::Create(Context, DC, SourceLocation(), SourceLocation(), &Context.Idents.get(name), Context.getTrivialTypeSourceInfo(BaseTy));
      return Context.getTypedefType(Typedef);
    }
  };

  class SubstituteType : public clang::TreeTransform<SubstituteType> {
    typedef TreeTransform<SubstituteType> TreeTransformS;
  public:
    SubstituteType(Sema &S, QualType F, QualType T) : TreeTransformS(S), From(F), To(T) {}
    QualType TransformType(TypeLocBuilder& TLB, TypeLoc Ty) {
      if(SemaRef.Context.hasSameType(Ty.getType(), From)) {
	Ty = SemaRef.Context.getTrivialTypeSourceInfo(To)->getTypeLoc();
      }
      return TreeTransformS::TransformType(TLB, Ty);
    }
    using TreeTransformS::TransformType;
  private:
    QualType From;
    QualType To;
  };

  // This class checks for arrays and other constructs that require a typedef
  // when used with UPCR_TLD_DEFINE.
  class CheckForArray : public clang::RecursiveASTVisitor<CheckForArray> {
  public:
    CheckForArray() : Found(false) {}
    bool VisitArrayType(ArrayType *) {
      Found = true;
      return false;
    }
    bool VisitFunctionType(FunctionType *) {
      Found = true;
      return false;
    }
    bool Found;
  };

  // The following expressions require dynamic initialization:
  // &global (If global is shared, then the address is set
  // dynamically, if it's local, then the address is thread
  // specific.
  class CheckForDynamicInitializer : public clang::RecursiveASTVisitor<CheckForDynamicInitializer> {
  public:
    CheckForDynamicInitializer() : Found(false) {}
    bool VisitDeclRefExpr(DeclRefExpr *E) {
      if(isa<VarDecl>(E->getDecl())) {
        Found = true;
        return false;
      }
      return true;
    }
    bool VisitExpr(Expr *E) {
      if(E->getType()->hasPointerToSharedRepresentation()) {
        Found = true;
        return false;
      }
      return true;
    }
    bool Found;
  };

  // Determines whether a typedef can safely be moved to
  // the global scope.  Variable arrays cannot be, since
  // they depend on local variables.
  class CheckForLocalType : public clang::RecursiveASTVisitor<CheckForLocalType> {
  public:
    CheckForLocalType() : Found(false) {}
    bool VisitVariableArrayType(VariableArrayType *) {
      Found = true;
      return false;
    }
    bool VisitUPCThreadArrayType(UPCThreadArrayType *) {
      Found = true;
      return false;
    }

    bool Found;
  };

  class RemoveUPCTransform : public clang::TreeTransform<RemoveUPCTransform> {
    typedef TreeTransform<RemoveUPCTransform> TreeTransformUPC;
  private:
    bool haveOffsetOf;
    bool haveVAArg;
  public:
    RemoveUPCTransform(Sema& S, UPCRDecls* D, const std::string& fileid)
      : TreeTransformUPC(S), AnonRecordID(0), StaticLocalVarID(0),
        Decls(D), FileString(fileid) {
      haveOffsetOf = haveVAArg = false;
    }
    bool HaveOffsetOf() { return haveOffsetOf; }
    ExprResult TransformOffsetOfExpr(OffsetOfExpr *E) {
      haveOffsetOf = true;
      return TreeTransformUPC::TransformOffsetOfExpr(E);
    }
    bool HaveVAArg() { return haveVAArg; }
    ExprResult TransformVAArgExpr(VAArgExpr *E) {
      haveVAArg = true;
      return TreeTransformUPC::TransformVAArgExpr(E);
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
    ExprResult BuildUPCRCall(FunctionDecl *FD, std::vector<Expr*>& args, SourceLocation Loc) {
      ExprResult Fn = SemaRef.BuildDeclRefExpr(FD, FD->getType(), VK_LValue, Loc);
      return SemaRef.BuildResolvedCallExpr(Fn.get(), FD, Loc, args, Loc);
    }
    ExprResult BuildUPCRCall(FunctionDecl *FD, std::vector<Expr*>& args) {
      return BuildUPCRCall(FD, args, SourceLocation());
    }
    ExprResult BuildUPCRDeclRef(VarDecl *VD) {
      return SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation());
    }
    Expr * CreateSimpleDeclRef(VarDecl *VD) {
      //return SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation()).get();
      //return dynamic_cast<Expr *>(SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation()));
      return dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(VD, VD->getType(), VK_LValue, SourceLocation()));
    }
    int AnonRecordID;
    int StaticLocalVarID;
    IdentifierInfo *getRecordDeclName(IdentifierInfo * OrigName) {
      return OrigName;
    }
    struct ArrayDimensionT {
      ArrayDimensionT(ASTContext& Context) :
	ArrayDimension(Context.getTypeSize(Context.getSizeType()), 1),
	HasThread(false),
	ElementSize(0),
	E(NULL)
      {}
      llvm::APInt ArrayDimension;
      bool HasThread;
      int64_t ElementSize; // Matches representation of CharUnits
      Expr *E;
    };
    ArrayDimensionT GetArrayDimension(QualType Ty) {
      ArrayDimensionT Result(SemaRef.Context);
      QualType ElemTy = Ty.getCanonicalType();
      while(const ArrayType *AT = dyn_cast<ArrayType>(ElemTy.getTypePtr())) {
	if(const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(AT)) {
	  Result.ArrayDimension *= CAT->getSize();
	} else if(const UPCThreadArrayType *TAT = dyn_cast<UPCThreadArrayType>(AT)) {
	  if(TAT->getThread()) {
	    Result.HasThread = true;
	  }
	  Result.ArrayDimension *= TAT->getSize();
	} else if(const VariableArrayType *VAT = dyn_cast<VariableArrayType>(AT)) {
	  Expr *Val = BuildParens(TransformExpr(VAT->getSizeExpr()).get()).get();
	  if(Result.E) {
	    Result.E = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, Result.E, Val).get();
	  } else {
	    Result.E = Val;
	  }
	} else if(isa<IncompleteArrayType>(AT)) {
	  Result.ArrayDimension = 0;
	} else {
	  assert(!"Other array types should not syntax check");
	}
	ElemTy = AT->getElementType();
      }
      Result.ElementSize = SemaRef.Context.getTypeSizeInChars(ElemTy).getQuantity();
      return Result;
    }
    Expr * MaybeAddParensForMultiply(Expr * E) {
      if(isa<ParenExpr>(E) || isa<IntegerLiteral>(E) ||
	 isa<CallExpr>(E))
	return E;
      else
	return BuildParens(E).get();
    }
    ExprResult MaybeAdjustForArray(const ArrayDimensionT & Dims, Expr * E, BinaryOperatorKind Op) {
      if(Dims.ArrayDimension == 1 && !Dims.E && !Dims.HasThread) {
	return E;
      } else {
	Expr *Dimension = IntegerLiteral::Create(SemaRef.Context, Dims.ArrayDimension, SemaRef.Context.getSizeType(), SourceLocation());
	if(Dims.HasThread) {
	  std::vector<Expr*> args;
	  Expr *Threads = BuildUPCRCall(Decls->upcr_threads, args).get();
	  Dimension = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, Dimension, Threads).get();
	}
	if(Dims.E) {
	  Dimension = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, Dimension, Dims.E).get();
	}
	if(Dims.HasThread || Dims.E) {
	  Dimension = BuildParens(Dimension).get();
	}
	return BuildParens(SemaRef.CreateBuiltinBinOp(SourceLocation(), Op, MaybeAddParensForMultiply(E), Dimension).get());
      }
    }
    std::vector<Expr*> BuildUPCBarrierArgs(Expr *ID) {
      ASTContext& Context = SemaRef.Context;
      bool isAnon = !ID;
      if(isAnon) {
	ID = IntegerLiteral::Create(Context, APInt(32, 0), Context.IntTy, SourceLocation());
      } else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(ID)) {
	QualType Ty = ICE->getSubExpr()->getType();
	if(isPointerToShared(Ty) || Ty.getQualifiers().hasShared()) {
	  ID = TransformExpr(ID).get();
	} else {
	  ID = TransformExpr(ICE->getSubExpr()).get();
	  TypeSourceInfo *Type;
	  if(ICE->getCastKind() == CK_PointerToIntegral) {
	    // Pointer types get 2 casts; this one silences "narrowing" warnings
	    Type = Context.getTrivialTypeSourceInfo(Context.getIntPtrType());
	    ID = SemaRef.BuildCStyleCastExpr(SourceLocation(), Type, SourceLocation(), ID).get();
	  }
	  Type = Context.getTrivialTypeSourceInfo(Context.IntTy);
	  ID = SemaRef.BuildCStyleCastExpr(SourceLocation(), Type, SourceLocation(), ID).get();
	}
      } else {
	ID = TransformExpr(ID).get();
      }
      std::vector<Expr*> args;
      args.push_back(ID);
      args.push_back(IntegerLiteral::Create(Context, APInt(32, isAnon), Context.IntTy, SourceLocation()));
      return args;
    }
    StmtResult TransformUPCNotifyStmt(UPCNotifyStmt *S) {
      std::vector<Expr*> args = BuildUPCBarrierArgs(S->getIdValue());
      Stmt *result = BuildUPCRCall(Decls->upcr_notify, args, S->getBeginLoc()).get();
      return result;
    }
    StmtResult TransformUPCWaitStmt(UPCWaitStmt *S) {
      std::vector<Expr*> args = BuildUPCBarrierArgs(S->getIdValue());
      Stmt *result = BuildUPCRCall(Decls->upcr_wait, args, S->getBeginLoc()).get();
      return result;
    }
    StmtResult TransformUPCBarrierStmt(UPCBarrierStmt *S) {
      std::vector<Expr*> args = BuildUPCBarrierArgs(S->getIdValue());
      Stmt *result = BuildUPCRCall(Decls->upcr_barrier, args, S->getBeginLoc()).get();
      return result;
    }
    StmtResult TransformUPCFenceStmt(UPCFenceStmt *S) {
      std::vector<Expr*> args;
      Stmt *result = BuildUPCRCall(Decls->upcr_poll, args, S->getBeginLoc()).get();
      return result;
    }
    ExprResult TransformUPCThreadExpr(UPCThreadExpr *E) {
      std::vector<Expr*> args;
      Expr *Call = BuildUPCRCall(Decls->upcr_threads, args).get();
      return SemaRef.BuildCStyleCastExpr(SourceLocation(), SemaRef.Context.getTrivialTypeSourceInfo(SemaRef.Context.IntTy), SourceLocation(), Call);
    }
    ExprResult TransformUPCMyThreadExpr(UPCMyThreadExpr *E) {
      std::vector<Expr*> args;
      Expr *Call = BuildUPCRCall(Decls->upcr_mythread, args).get();
      return SemaRef.BuildCStyleCastExpr(SourceLocation(), SemaRef.Context.getTrivialTypeSourceInfo(SemaRef.Context.IntTy), SourceLocation(), Call);
    }
    ExprResult TransformInitializer(Expr *Init, bool CXXDirectInit) {
      if(!Init)
	return Init;

      // Have to handle this separately, as TreeTransform
      // strips off ImplicitCastExprs in TransformInitializer.
      if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Init)) {
	if((ICE->getCastKind() == CK_LValueToRValue && ICE->getSubExpr()->getType().getQualifiers().hasShared()) ||
	   isPointerToShared(ICE->getSubExpr()->getType())) {
	  return TransformExpr(ICE);
	} else {
	  ExprResult UPCCast = MaybeTransformUPCRCast(ICE);
	  if(!UPCCast.isInvalid())
	    return UPCCast;
	  return TransformInitializer(ICE->getSubExpr(), CXXDirectInit);
	}
      }

      return TreeTransformUPC::TransformInitializer(Init, CXXDirectInit);
    }
    ExprResult TransformCStyleCastExpr(CStyleCastExpr *E) {
      ExprResult UPCCast = MaybeTransformUPCRCast(E);
      if(!UPCCast.isInvalid()) {
	return UPCCast;
      } else {
	// The default transform strips off implicit casts
	TypeSourceInfo *Type = TransformType(E->getTypeInfoAsWritten());
	if (!Type)
	  return ExprError();

	ExprResult SubExpr = TransformExpr(E->getSubExpr());
	if (SubExpr.isInvalid())
	  return ExprError();
	
	return RebuildCStyleCastExpr(E->getLParenLoc(),
				     Type,
				     E->getRParenLoc(),
				     SubExpr.get());
      }
    }
    ExprResult TransformImplicitCastExpr(ImplicitCastExpr *E) {
      if(E->getCastKind() == CK_LValueToRValue && E->getSubExpr()->getType().getQualifiers().hasShared()) {
	return BuildUPCRLoad(TransformExpr(E->getSubExpr()).get(), E->getSubExpr()->getType());
      } else {
	ExprResult UPCCast = MaybeTransformUPCRCast(E);
	if(!UPCCast.isInvalid()) {
	  return UPCCast;
	}
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
    bool isLiteralInt(const Expr *E, uint64_t value) {
      const IntegerLiteral *Lit = dyn_cast<IntegerLiteral>(E->IgnoreParenCasts());
      return (Lit && Lit->getValue() == value);
    }
    bool typeFitsUPCRValuePutGet(QualType Ty) {
      // FIXME: pointers-to-shared may fit, but since we cannot cast freely between
      //        them and upcr_register_value_t, we also can't xfer them by value.
      if(isPointerToShared(Ty)) return false;
      return Ty->isSpecificBuiltinType(BuiltinType::Float) ||
             Ty->isSpecificBuiltinType(BuiltinType::Double) ||
             ((Ty->isIntegralOrEnumerationType() || Ty->isPointerType()) &&
              (SemaRef.Context.getTypeSize(Ty) <= SemaRef.Context.getTypeSize(Decls->upcr_register_value_t)));
    }
    Expr *FoldUPCRLoadStore(Expr* &E, bool &Phaseless) {
      Expr *Offset = NULL;
      while (CallExpr *CE = dyn_cast<CallExpr>(E->IgnoreParens())) {
        FunctionDecl *FD = CE->getDirectCallee();
        if (FD == Decls->UPCR_SHARED_TO_PSHARED || FD == Decls->UPCR_PSHARED_TO_SHARED) {
          // Fold phased/phaseless conversion into choice of Accessor
          // NOTE: Dropping a shared_to_pshared() in this manner is NOT a correct
          // transform if any definite pointer-to-shared arithmetic were then applied.
          // It is acceptible here ONLY because Put and Get don't use the phase.
          E = CE->getArg(0);
          Phaseless = !Phaseless;
        } else if (FD == Decls->UPCR_ADD_PSHAREDI) {
          // Fold (non-zero) indefinite address arithmetic into the Offset
          E = CE->getArg(0);
          Expr *Elemsz = CE->getArg(1);
          Expr *Inc = CE->getArg(2);
          Expr *NewOffset;
          if (isLiteralInt(Elemsz,1)) {
            NewOffset = Inc;
          } else {
            Elemsz = MaybeAddParensForMultiply(Elemsz);
            Inc = MaybeAddParensForMultiply(Inc);
            NewOffset = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, Elemsz, Inc).get();
          }
          if (Offset) {
            Offset = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Add, Offset, NewOffset).get();
          } else {
            Offset = NewOffset;
          }
        } else {
          break;
        }
      }
      if (Offset) return Offset;
      return CreateInteger(SemaRef.Context.getSizeType(), 0);
    }
    // If LoadVar is passed, then the result will contain an assignment to it.
    // Otherwise the result will use a temporary only if necessary.
    // Regardless, the value of the expression will be the result of the Load.
    Expr *BuildUPCRLoad(Expr * Ptr, QualType Ty, Expr * LoadVar = NULL) {
      Qualifiers Quals = Ty.getQualifiers();
      bool Phaseless = isPhaseless(Ty);
      bool Strict = Quals.hasStrict();
      // Try to fold offset and phased/phaseless conversions:
      Expr *Offset = FoldUPCRLoadStore(Ptr, Phaseless);
      std::vector<Expr*> args;
      Expr *Result;
      QualType ResultType = TransformType(Ty).getUnqualifiedType();
      if(typeFitsUPCRValuePutGet(ResultType)) {
	// Case 1.  Get by value, with type cast if necesssary
	args.push_back(Ptr);
	args.push_back(Offset);
	UPCRCommFn *Accessor;
	if(ResultType->isSpecificBuiltinType(BuiltinType::Float)) {
	  Accessor = &Decls->UPCR_GET_FVAL;
	} else if(ResultType->isSpecificBuiltinType(BuiltinType::Double)) {
	  Accessor = &Decls->UPCR_GET_DVAL;
	} else {
	  Accessor = &Decls->UPCR_GET_IVAL;
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(),SemaRef.Context.getTypeSizeInChars(Ty).getQuantity()));
	}
	Result = BuildUPCRCall((*Accessor)(Phaseless,Strict), args).get();
	// NOTE: Without a cast the float and double cases yield an assertion failure!?
	TypeSourceInfo *CastTo = SemaRef.Context.getTrivialTypeSourceInfo(ResultType);
	Result = SemaRef.BuildCStyleCastExpr(SourceLocation(), CastTo, SourceLocation(), Result).get();
	if(LoadVar) {
	  Result = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, LoadVar, Result).get();
	}
	Result = BuildParens(Result).get();
      } else {
	// Case 2.  Get by reference, to callers LoadVar if passed
	VarDecl *TmpVar = NULL;
	if (!LoadVar) { // Create a LoadVar if the caller doesn't provide one
	  TmpVar = CreateTmpVar(ResultType);
	  LoadVar = CreateSimpleDeclRef(TmpVar);
	}
	args.push_back(SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, LoadVar).get());
	args.push_back(Ptr);
	args.push_back(Offset);
	args.push_back(CreateInteger(SemaRef.Context.getSizeType(),SemaRef.Context.getTypeSizeInChars(Ty).getQuantity()));
	Result = BuildUPCRCall(Decls->UPCR_GET(Phaseless,Strict), args).get();
	if(TmpVar) Result = BuildParens(BuildComma(Result, CreateSimpleDeclRef(TmpVar)).get()).get();
      }
      return Result;
    }
    ExprResult BuildUPCRSharedToPshared(Expr *Ptr) {
      CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens());
      FunctionDecl *Child = CE? CE->getDirectCallee() : 0;
      if(Child == Decls->UPCR_PSHARED_TO_SHARED) {
	// upcr_shared_to_pshared(pshared_to_shared(p)) -> p
	return ExprResult(CE->getArg(0));
      } else if(Child == Decls->UPCR_SHARED_RESETPHASE) {
	// shared_to_pshared(resetphase(p)) -> shared_to_pshared(p)
	Ptr = CE->getArg(0);
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      return BuildUPCRCall(Decls->UPCR_SHARED_TO_PSHARED, args);
    }
    ExprResult BuildUPCRPsharedToShared(Expr *Ptr) {
      CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens());
      FunctionDecl *Child = CE? CE->getDirectCallee() : 0;
      if(Child == Decls->UPCR_SHARED_TO_PSHARED) {
	// pshared_to_shared(shared_to_pshared(p)) -> resetphase(p)
	return BuildUPCRSharedResetPhase(CE->getArg(0));
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      return BuildUPCRCall(Decls->UPCR_PSHARED_TO_SHARED, args);
    }
    ExprResult BuildUPCRSharedResetPhase(Expr *Ptr) {
      CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens());
      FunctionDecl *Child = CE? CE->getDirectCallee() : 0;
      if(Child == Decls->UPCR_SHARED_RESETPHASE) {
	// resetphase(resetphase(p)) -> resetphase(p)
	return ExprResult(Ptr);
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      return BuildUPCRCall(Decls->UPCR_SHARED_RESETPHASE, args);
    }
    ExprResult MaybeTransformUPCRCast(CastExpr *E) {
      if(E->getCastKind() == CK_UPCSharedToLocal) {
	bool Phaseless = isPhaseless(E->getSubExpr()->getType()->getAs<PointerType>()->getPointeeType());
	FunctionDecl *Accessor = Phaseless? Decls->UPCR_PSHARED_TO_LOCAL : Decls->UPCR_SHARED_TO_LOCAL;
	std::vector<Expr*> args;
	args.push_back(TransformExpr(E->getSubExpr()).get());
	ExprResult Result = BuildUPCRCall(Accessor, args);
	TypeSourceInfo *Ty = SemaRef.Context.getTrivialTypeSourceInfo(TransformType(E->getType()));
	return SemaRef.BuildCStyleCastExpr(SourceLocation(), Ty, SourceLocation(), Result.get());
      } else if(E->getCastKind() == CK_NullToPointer && isPointerToShared(E->getType())) {
	bool Phaseless = isPhaseless(E->getType()->getAs<PointerType>()->getPointeeType());
	return BuildUPCRDeclRef(Phaseless? Decls->upcr_null_pshared : Decls->upcr_null_shared);
      } else if((E->getCastKind() == CK_BitCast  ||
		 E->getCastKind() == CK_UPCBitCastZeroPhase) &&
		isPointerToShared(E->getType())) {
	QualType DstPointee = E->getType()->getAs<PointerType>()->getPointeeType();
	QualType SrcPointee = E->getSubExpr()->getType()->getAs<PointerType>()->getPointeeType();
	ExprResult Result = TransformExpr(E->getSubExpr());
	if(isPhaseless(DstPointee) && !isPhaseless(SrcPointee)) {
	  return BuildUPCRSharedToPshared(Result.get());
	} else if(!isPhaseless(DstPointee) && isPhaseless(SrcPointee)) {
	  return BuildUPCRPsharedToShared(Result.get());
	} else if(!isPhaseless(DstPointee) && !isPhaseless(SrcPointee) &&
		  E->getCastKind() == CK_UPCBitCastZeroPhase) {
	  return BuildUPCRSharedResetPhase(Result.get());
	} else {
	  return Result;
	}
      } else if(E->getCastKind() == CK_PointerToIntegral &&
		isPointerToShared(E->getSubExpr()->getType())) {
	bool Phaseless = isPhaseless(E->getSubExpr()->getType()->getAs<PointerType>()->getPointeeType());
	FunctionDecl *Accessor = Phaseless? Decls->UPCR_ADDRFIELD_PSHARED : Decls->UPCR_ADDRFIELD_SHARED;
	std::vector<Expr*> args;
	args.push_back(TransformExpr(E->getSubExpr()).get());
	Expr *Result = BuildUPCRCall(Accessor, args).get();
	TypeSourceInfo *Type = SemaRef.Context.getTrivialTypeSourceInfo(TransformType(E->getType()));
	return SemaRef.BuildCStyleCastExpr(SourceLocation(), Type, SourceLocation(), Result);
      }
      return ExprError();
    }
    ExprResult BuildUPCRStore(Expr * LHS, Expr * RHS, QualType Ty, bool ReturnValue = true) {
      Qualifiers Quals = Ty.getQualifiers(); 
      bool Phaseless = isPhaseless(Ty);
      bool Strict = Quals.hasStrict();
      // Try to fold offset and phased/phaseless conversions:
      Expr *Offset = FoldUPCRLoadStore(LHS, Phaseless);
      // Select the default function to call
      UPCRCommFn *Accessor = &Decls->UPCR_PUT;
      Expr *SetTmp = NULL;
      Expr *SrcArg = NULL;
      Expr *RetVal = NULL;
      bool NeedSize = true;
      QualType ResultType = TransformType(Ty).getUnqualifiedType();
      QualType RHSType = RHS->getType().getUnqualifiedType();
      if(typeFitsUPCRValuePutGet(ResultType)) {
	if (RHS->isLValue() && !ReturnValue) {
	  // Case 1. Put RHS by value, with type cast if necessary
	  SrcArg = RHS;
	  if(!SemaRef.Context.typesAreCompatible(ResultType, RHSType)) {
	    TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(ResultType);
	    SrcArg = SemaRef.BuildCStyleCastExpr(SourceLocation(), TSI, SourceLocation(), SrcArg).get();
	  }
	} else {
	  // Case 2. Store value of RHS in a temporary. which is Put by value
	  // If(ReturnValue) then the temporary's value is returned
	  VarDecl *TmpVar = CreateTmpVar(ResultType);
	  SetTmp = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, CreateSimpleDeclRef(TmpVar), RHS).get();
	  SrcArg = CreateSimpleDeclRef(TmpVar);
	  if(ReturnValue) RetVal = CreateSimpleDeclRef(TmpVar);
	}
	if(ResultType->isSpecificBuiltinType(BuiltinType::Float)) {
	  Accessor = &Decls->UPCR_PUT_FVAL;
	  NeedSize = false;
	} else if(ResultType->isSpecificBuiltinType(BuiltinType::Double)) {
	  Accessor = &Decls->UPCR_PUT_DVAL;
	  NeedSize = false;
	} else {
	  TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(Decls->upcr_register_value_t);
	  SrcArg = SemaRef.BuildCStyleCastExpr(SourceLocation(), TSI, SourceLocation(), SrcArg).get();
	  Accessor = &Decls->UPCR_PUT_IVAL;
	}
      } else if (RHS->isLValue() && !ReturnValue &&
		 SemaRef.Context.typesAreCompatible(ResultType, RHSType)) {
	// Case 3. Put RHS by reference (safe because no return or type conversion required)
	SrcArg = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, RHS).get();
      } else {
	// Case 4. Store value of RHS in a temporary which is Put by reference
	// If(ReturnValue) then the temporary's value is returned
	VarDecl *TmpVar = CreateTmpVar(ResultType);
	SetTmp = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, CreateSimpleDeclRef(TmpVar), RHS).get();
	SrcArg = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, CreateSimpleDeclRef(TmpVar)).get();
	if(ReturnValue) RetVal = CreateSimpleDeclRef(TmpVar);
      }
      std::vector<Expr*> args;
      args.push_back(LHS);
      args.push_back(Offset);
      args.push_back(SrcArg);
      if(NeedSize) {
	args.push_back(CreateInteger(SemaRef.Context.getSizeType(),SemaRef.Context.getTypeSizeInChars(Ty).getQuantity()));
      }
      ExprResult Result = BuildUPCRCall((*Accessor)(Phaseless,Strict), args);
      if(SetTmp || RetVal) {
	if(SetTmp) Result = BuildComma(SetTmp, Result.get());
	if(RetVal) Result = BuildComma(Result.get(), RetVal);
	Result = BuildParens(Result.get());
      }
      return Result;
    }
    ExprResult BuildUPCRAddPsharedI(Expr *Ptr, int64_t ElemSz, Expr *Inc) {
      if(isLiteralInt(Inc,0)) return Ptr; // No-op
      if(CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens())) {
	if(CE->getDirectCallee() == Decls->UPCR_ADD_PSHAREDI) {
	  // Can fold nested UPCR_ADD_PSHAREDI regardless of whether ElemSz matches
	  Ptr = CE->getArg(0);
	  if(isLiteralInt(CE->getArg(1),ElemSz)) {
	    // Can fold simply if ElemSz matches:
	    Inc = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Add, Inc, CE->getArg(2)).get();
	  } else {
	    // Can fold other cases with some extra work:
	    Expr *Op1 = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul,
						   CreateInteger(SemaRef.Context.getSizeType(),ElemSz),
						   MaybeAddParensForMultiply(Inc)).get();
	    Expr *Op2 = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, CE->getArg(1),
						   MaybeAddParensForMultiply(CE->getArg(2))).get();
	    Inc = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Add, Op1, Op2).get();
	    ElemSz = 1;
	  }
	}
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElemSz));
      args.push_back(Inc);
      return BuildUPCRCall(Decls->UPCR_ADD_PSHAREDI, args);
    }
    ExprResult BuildUPCRAddPshared1(Expr *Ptr, int64_t ElemSz, Expr *Inc) {
      if(isLiteralInt(Inc,0)) return Ptr; // No-op
      if(CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens())) {
	// Can fold any nested UPCR_ADD_PSHARED1 if ElemSz matches:
	if((CE->getDirectCallee() == Decls->UPCR_ADD_PSHARED1) &&
	   isLiteralInt(CE->getArg(1),ElemSz)) {
	  Ptr = CE->getArg(0);
	  Inc = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Add, Inc, CE->getArg(2)).get();
	}
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElemSz));
      args.push_back(Inc);
      return BuildUPCRCall(Decls->UPCR_ADD_PSHARED1, args);
    }
    ExprResult BuildUPCRAddShared(Expr *Ptr, int64_t ElemSz, Expr *Inc, uint32_t BlockSz) {
      if(isLiteralInt(Inc,0)) return Ptr; // No-op
      if(CallExpr *CE = dyn_cast<CallExpr>(Ptr->IgnoreParens())) {
	// Can fold any nested UPCR_ADD_SHARED if ElemSz and BlockSz each match:
	if((CE->getDirectCallee() == Decls->UPCR_ADD_SHARED) &&
	   isLiteralInt(CE->getArg(1),ElemSz) && isLiteralInt(CE->getArg(3),BlockSz)) {
	  Ptr = CE->getArg(0);
	  Inc = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Add, Inc, CE->getArg(2)).get();
	}
      }
      std::vector<Expr*> args;
      args.push_back(Ptr);
      args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElemSz));
      args.push_back(Inc);
      args.push_back(CreateInteger(SemaRef.Context.getSizeType(), BlockSz));
      return BuildUPCRCall(Decls->UPCR_ADD_SHARED, args);
    }
    ExprResult CreateUPCPointerArithmetic(Expr *Ptr, Expr *IntVal, QualType PtrTy) {
      QualType PointeeType = PtrTy->getAs<PointerType>()->getPointeeType();
      ArrayDimensionT Dims = GetArrayDimension(PointeeType);
      int64_t ElementSize = Dims.ElementSize;
      IntVal = MaybeAdjustForArray(Dims, IntVal, BO_Mul).get();
      uint32_t LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
      if(LayoutQualifier == 0) {
	return BuildUPCRAddPsharedI(Ptr, ElementSize, IntVal);
      } else if(isPhaseless(PointeeType) && LayoutQualifier == 1) {
	return BuildUPCRAddPshared1(Ptr, ElementSize, IntVal);
      } else {
	return BuildUPCRAddShared(Ptr, ElementSize, IntVal, LayoutQualifier);
      }
    }
    ExprResult CreateArithmeticExpr(Expr *LHS, Expr *RHS, QualType LHSTy, BinaryOperatorKind Op) {
      if(isPointerToShared(LHSTy)) {
	if(Op == BO_Sub) {
	  RHS = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Minus, RHS).get();
	}
	return CreateUPCPointerArithmetic(LHS, RHS, LHSTy);
      } else {
	return SemaRef.CreateBuiltinBinOp(SourceLocation(), Op, LHS, RHS);
      }
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
	Expr * TmpPtr = dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(TmpPtrDecl, PtrType, VK_LValue, SourceLocation()));
	Expr * SaveArg = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr, BuildParens(TransformExpr(E->getSubExpr()).get()).get()).get();
	QualType ResultType = TransformType(ArgType.getUnqualifiedType());
	Expr * LoadVar = CreateSimpleDeclRef(CreateTmpVar(ResultType));
	Expr * LoadExpr = BuildUPCRLoad(TmpPtr, ArgType, LoadVar);
	Expr * NewVal = CreateArithmeticExpr(LoadVar, CreateInteger(SemaRef.Context.IntTy, 1), ArgType, E->isIncrementOp()?BO_Add:BO_Sub).get();

	if(E->isPrefix()) {
	  Expr * Result = BuildUPCRStore(TmpPtr, NewVal, ArgType).get();
	  return BuildParens(BuildComma(SaveArg, BuildComma(LoadExpr, Result).get()).get());
	} else {
	  Expr * Result = BuildUPCRStore(TmpPtr, NewVal, ArgType, false).get();
	  return BuildParens(BuildComma(SaveArg, BuildComma(LoadExpr, BuildComma(Result, LoadVar).get()).get()).get());
	}
      } else if(isPointerToShared(ArgType) && E->isIncrementDecrementOp()) {
	QualType TmpPtrType = SemaRef.Context.getPointerType(TransformType(ArgType));
	VarDecl * TmpPtrDecl = CreateTmpVar(TmpPtrType);
	Expr * TmpPtr = CreateSimpleDeclRef(TmpPtrDecl);
        Expr * Setup = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr, SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, TransformExpr(E->getSubExpr()).get()).get()).get();
	Expr * Access = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Deref, TmpPtr).get();

	VarDecl * TmpValDecl = CreateTmpVar(TransformType(ArgType).getUnqualifiedType());
	Expr * TmpVal = CreateSimpleDeclRef(TmpValDecl);
	Expr * Expr1;
	Expr * Expr2;
	// Uses TmpVal such that Access is read exactly once (in case it is volatile)
	if(E->isPostfix()) {
	  Expr1 = Access;
	  Expr2 = CreateArithmeticExpr(TmpVal, CreateInteger(SemaRef.Context.IntTy, 1),
					ArgType, E->isIncrementOp()?BO_Add:BO_Sub).get();
	} else {
	  Expr1 = CreateArithmeticExpr(Access, CreateInteger(SemaRef.Context.IntTy, 1),
					ArgType, E->isIncrementOp()?BO_Add:BO_Sub).get();
	  Expr2 = TmpVal;
	}
	Expr1 = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpVal, Expr1).get();
	Expr2 = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, Access, Expr2).get();
	return BuildParens(BuildComma(Setup, BuildComma(Expr1, BuildComma(Expr2, TmpVal).get()).get()).get());
      } else if(isPointerToShared(ArgType) && E->getOpcode() == UO_LNot) {
	bool Phaseless = isPhaseless(ArgType->getAs<PointerType>()->getPointeeType());
	std::vector<Expr*> args;
	args.push_back(TransformExpr(E->getSubExpr()).get());
	return BuildUPCRCall(Phaseless?Decls->UPCR_ISNULL_PSHARED:Decls->UPCR_ISNULL_SHARED, args);
      } else {
	return TreeTransformUPC::TransformUnaryOperator(E);
      }
    }
    ExprResult TransformBinaryOperator(BinaryOperator *E) {
      // Catch assignment to shared variables
      if(E->getOpcode() == BO_Assign && E->getLHS()->getType().getQualifiers().hasShared()) {
	Expr *LHS = TransformExpr(E->getLHS()).get();
	Expr *RHS = TransformExpr(E->getRHS()).get();
	return BuildUPCRStore(LHS, RHS, E->getLHS()->getType());
      } else if (E->getOpcode() == BO_LAnd || E->getOpcode() == BO_LOr) {
        // handle pointers-to-shared in && and ||
	bool LHSIsShared = isPointerToShared(E->getLHS()->getType());
	bool RHSIsShared = isPointerToShared(E->getRHS()->getType());
        if(LHSIsShared || RHSIsShared) {
          ExprResult LHS = TransformCondition(E->getLHS());
          ExprResult RHS = TransformCondition(E->getRHS());
          return RebuildBinaryOperator(E->getOperatorLoc(), E->getOpcode(),
                                       LHS.get(), RHS.get());
        }
      } else {
	Expr *LHS = E->getLHS();
	Expr *RHS = E->getRHS();
	bool LHSIsShared = isPointerToShared(E->getLHS()->getType());
	bool RHSIsShared = isPointerToShared(E->getRHS()->getType());
	if(LHSIsShared && RHSIsShared && E->getOpcode() == BO_Sub) {
	  // Pointer - Pointer
	  ExprResult Result;
	  QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	  ArrayDimensionT Dims = GetArrayDimension(PointeeType);
	  int64_t ElementSize = Dims.ElementSize;
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(TransformExpr(RHS).get());
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	  uint32_t LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	  if(LayoutQualifier == 0) {
	    Result = BuildUPCRCall(Decls->UPCR_SUB_PSHAREDI, args);
	  } else if(isPhaseless(PointeeType) && LayoutQualifier == 1) {
	    Result = BuildUPCRCall(Decls->UPCR_SUB_PSHARED1, args);
	  } else {
	    args.push_back(CreateInteger(SemaRef.Context.getSizeType(), LayoutQualifier));
	    Result = BuildUPCRCall(Decls->UPCR_SUB_SHARED, args);
	  }
	  return MaybeAdjustForArray(Dims, Result.get(), BO_Div);
	} else if((LHSIsShared || RHSIsShared) && (E->getOpcode() == BO_Add || E->getOpcode() == BO_Sub)) {
	  // Pointer +/- Integer
	  if(RHSIsShared) { std::swap(LHS, RHS); }
	  Expr *IntVal = TransformExpr(RHS).get();
	  if(E->getOpcode() == BO_Sub) {
	    IntVal = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Minus, IntVal).get();
	  }
	  return CreateUPCPointerArithmetic(TransformExpr(LHS).get(), IntVal, LHS->getType());
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
	  int64_t ElementSize = SemaRef.Context.getTypeSizeInChars(PointeeType).getQuantity();
	  std::vector<Expr*> args;
	  args.push_back(TransformExpr(LHS).get());
	  args.push_back(TransformExpr(RHS).get());
	  args.push_back(CreateInteger(SemaRef.Context.getSizeType(), ElementSize));
	  uint32_t LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
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
      return TreeTransformUPC::TransformBinaryOperator(E);
    }
    ExprResult TransformCompoundAssignOperator(CompoundAssignOperator *E) {
      if(E->getLHS()->getType().getQualifiers().hasShared()) {
	QualType Ty = E->getLHS()->getType();
	bool Phaseless = isPhaseless(Ty);
	QualType PtrType = Phaseless? Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	VarDecl * TmpPtrDecl = CreateTmpVar(PtrType);
	BinaryOperatorKind Opc = BinaryOperator::getOpForCompoundAssignment(E->getOpcode());
	Expr * TmpPtr = dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(TmpPtrDecl, PtrType, VK_LValue, SourceLocation()));
	Expr * SaveLHS = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr, BuildParens(TransformExpr(E->getLHS()).get()).get()).get();
	Expr * RHS = BuildParens(TransformExpr(E->getRHS()).get()).get();
	Expr * LHSVal = BuildUPCRLoad(TmpPtr, Ty);
	Expr * OpResult = CreateArithmeticExpr(LHSVal, RHS, Ty, Opc).get();
	Expr * Result = BuildUPCRStore(TmpPtr, OpResult, Ty).get();
	return BuildParens(BuildComma(SaveLHS, Result).get());
      }	else if(isPointerToShared(E->getLHS()->getType())) {
	QualType Ty = E->getLHS()->getType();
	BinaryOperatorKind Opc = BinaryOperator::getOpForCompoundAssignment(E->getOpcode());
	QualType PtrType = SemaRef.Context.getPointerType(TransformType(Ty));
	VarDecl * TmpPtrDecl = CreateTmpVar(PtrType);
	Expr * TmpPtr = CreateSimpleDeclRef(TmpPtrDecl);
	Expr * LHSPtr = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_AddrOf, BuildParens(TransformExpr(E->getLHS()).get()).get()).get();
	Expr * SetPtr = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpPtr,
						   LHSPtr).get();
	Expr * TmpVar = SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Deref, TmpPtr).get();
	Expr * OpResult = CreateArithmeticExpr(TmpVar, TransformExpr(E->getRHS()).get(), Ty, Opc).get();
	Expr * Result = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, TmpVar, OpResult).get();
	return BuildParens(BuildComma(SetPtr, Result).get());
      } else {
	return TreeTransformUPC::TransformCompoundAssignOperator(E);
      }
    }
    ExprResult TransformArraySubscriptExpr(ArraySubscriptExpr *E) {
      if(isPointerToShared(E->getBase()->getType())) {
	Expr *LHS = E->getBase();
	Expr *RHS = E->getIdx();
	QualType PointeeType = LHS->getType()->getAs<PointerType>()->getPointeeType();
	ArrayDimensionT Dims = GetArrayDimension(PointeeType);
	int64_t ElementSize = Dims.ElementSize;
	Expr *Ptr = TransformExpr(LHS).get();
	Expr *IntVal = TransformExpr(RHS).get();
	IntVal = MaybeAdjustForArray(Dims, IntVal, BO_Mul).get();
	uint32_t LayoutQualifier = PointeeType.getQualifiers().getLayoutQualifier();
	if(LayoutQualifier == 0) {
	  return BuildUPCRAddPsharedI(Ptr, ElementSize, IntVal);
	} else if(LayoutQualifier == 1) {
	  return BuildUPCRAddPshared1(Ptr, ElementSize, IntVal);
	} else {
	  return BuildUPCRAddShared(Ptr, ElementSize, IntVal, LayoutQualifier);
	}
      } else {
	return TreeTransformUPC::TransformArraySubscriptExpr(E);
      }
    }
    ExprResult TransformMemberExpr(MemberExpr *E) {
      Expr *Base = E->getBase();
      QualType BaseType = Base->getType();
      if(const PointerType *PT = BaseType->getAs<PointerType>()) {
	BaseType = PT->getPointeeType();
      }
      if(BaseType.getQualifiers().hasShared()) {
	ValueDecl * FD = E->getMemberDecl();
	Expr *NewBase = TransformExpr(Base).get();
	if(!isPhaseless(BaseType)) {
	  NewBase = BuildUPCRSharedToPshared(NewBase).get();
	}
	CharUnits Offset = SemaRef.Context.toCharUnitsFromBits(SemaRef.Context.getFieldOffset(FD));
	Expr *IntVal = CreateInteger(SemaRef.Context.getSizeType(), Offset.getQuantity());
	return BuildUPCRAddPsharedI(NewBase, 1, IntVal);
      } else {
	return TreeTransformUPC::TransformMemberExpr(E);
      }
    }
    ExprResult TransformUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr *E) {
      switch(E->getKind()) {
      case UETT_UPC_LocalSizeOf:
      case UETT_UPC_BlockSizeOf:
      case UETT_UPC_ElemSizeOf:
	{
	llvm::APSInt Value;
	SemaRef.VerifyIntegerConstantExpression(E, &Value);
	return IntegerLiteral::Create(SemaRef.Context, Value, E->getType(), SourceLocation());
	}
      case UETT_SizeOf:
	{
	  // shared types can be changed by the transformation
	  // we need to calculate this up front.
	  if(E->getTypeOfArgument().getQualifiers().hasShared()) {
	    ArrayDimensionT Dims = GetArrayDimension(E->getTypeOfArgument());
	    int64_t ElementSize = Dims.ElementSize;
	    Expr *IntVal = CreateInteger(SemaRef.Context.getSizeType(), ElementSize);
	    return MaybeAdjustForArray(Dims, IntVal, BO_Mul);
	  }
	  // fallthrough
	}
      default:
	return TreeTransformUPC::TransformUnaryExprOrTypeTraitExpr(E);
      }
    }
    ExprResult BuildTLDRefExpr(DeclRefExpr *DRE) {
      QualType Ty = DRE->getDecl()->getType();
      TypeSourceInfo *PtrTy = SemaRef.Context.getTrivialTypeSourceInfo(SemaRef.Context.getPointerType(Ty));
      std::vector<Expr*> args;
      args.push_back(DRE);
      Expr *Call = BuildUPCRCall(Decls->UPCR_TLD_ADDR, args).get();
      return BuildParens(SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_Deref, SemaRef.BuildCStyleCastExpr(SourceLocation(), PtrTy, SourceLocation(), Call).get()).get());
    }
    ExprResult TransformDeclRefExpr(DeclRefExpr *E) {
      ExprResult Result = TreeTransformUPC::TransformDeclRefExpr(E);
      if(!Result.isInvalid()) {
        if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Result.get())) {
          if(isUPCThreadLocal(DRE->getDecl())) {
            Result = BuildTLDRefExpr(DRE);
          }
        }
      }
      return Result;
    }
    StmtResult TransformUPCForAllStmt(UPCForAllStmt *S) {
      // Transform the initialization statement
      StmtResult Init = getDerived().TransformStmt(S->getInit());


      // Transform the condition
      Sema::ConditionResult Cond = getDerived().TransformCondition(
        S->getForLoc(), S->getConditionVariable(), S->getCond(),
        Sema::ConditionKind::Boolean);
      if (Cond.isInvalid())
        return StmtError();

      // Transform the increment
      ExprResult Inc = TransformExpr(S->getInc());
      if (Inc.isInvalid())
	return StmtError();
      
      Sema::FullExprArg FullInc(getSema().MakeFullExpr(Inc.get()));

      // Transform the body
      StmtResult Body = TransformStmt(S->getBody());

      StmtResult PlainFor = SemaRef.ActOnForStmt(S->getForLoc(), S->getLParenLoc(),
						 Init.get(), Cond,
						 FullInc, S->getRParenLoc(), Body.get());

      // If the thread affinity is not specified, upc_forall is
      // the same as a for loop.
      if(!S->getAfnty()) {
	return PlainFor;
      }

      ExprResult Afnty = TransformExpr(S->getAfnty());
      ExprResult ThreadTest_;
      if(isPointerToShared(S->getAfnty()->getType())) {
	bool Phaseless = isPhaseless(S->getAfnty()->getType()->getAs<PointerType>()->getPointeeType());
	std::vector<Expr*> args;
	args.push_back(Afnty.get());
	ThreadTest_ = BuildUPCRCall(Phaseless?Decls->upcr_hasMyAffinity_pshared:Decls->upcr_hasMyAffinity_shared, args);
      } else {
	std::vector<Expr*> args;
	Expr * Affinity = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Rem, BuildParens(Afnty.get()).get(), BuildUPCRCall(Decls->upcr_threads, args).get()).get();
	ThreadTest_ = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_EQ, Affinity, BuildUPCRCall(Decls->upcr_mythread, args).get());
      }

      Sema::ConditionResult ThreadTest = SemaRef.ActOnCondition(nullptr, SourceLocation(), ThreadTest_.get(), Sema::ConditionKind::Boolean);

      StmtResult UPCBody = SemaRef.ActOnIfStmt(SourceLocation(), false, nullptr, ThreadTest, Body.get(), SourceLocation(), nullptr);

      StmtResult UPCFor = SemaRef.ActOnForStmt(S->getForLoc(), S->getLParenLoc(),
						 Init.get(), Cond,
						 FullInc, S->getRParenLoc(), UPCBody.get());

      Expr * ForAllCtrl_ = CreateSimpleDeclRef(Decls->upcrt_forall_control);
      {
        if (SemaRef.Context.getLangOpts().UPCTLDEnable)
          ForAllCtrl_ = BuildTLDRefExpr(dyn_cast<DeclRefExpr>(ForAllCtrl_)).get();
      }
      
      Sema::ConditionResult ForAllCtrl = SemaRef.ActOnCondition(
        nullptr, SourceLocation(), ForAllCtrl_, Sema::ConditionKind::Boolean);

      StmtResult UPCForWrapper;
      {
	Sema::CompoundScopeRAII BodyScope(SemaRef);
	SmallVector<Stmt*, 8> Statements;
	Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, ForAllCtrl_, CreateInteger(SemaRef.Context.IntTy, 1)).get());
	Statements.push_back(UPCFor.get());
	Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, ForAllCtrl_, CreateInteger(SemaRef.Context.IntTy, 0)).get());

	UPCForWrapper = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
      }

      StmtResult PlainForWrapper;
      {
	Sema::CompoundScopeRAII BodyScope(SemaRef);
	PlainForWrapper = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), PlainFor.get(), false);
      }

      return SemaRef.ActOnIfStmt(SourceLocation(), false, nullptr, ForAllCtrl, PlainForWrapper.get(), SourceLocation(), UPCForWrapper.get());
    }
    ExprResult TransformCondition(Expr *E) {
      ExprResult Result = TransformExpr(E);
      if(isPointerToShared(E->getType())) {
	bool Phaseless = isPhaseless(E->getType()->getAs<PointerType>()->getPointeeType());
	std::vector<Expr*> args;
	args.push_back(Result.get());
	ExprResult Test = BuildUPCRCall(Phaseless?Decls->UPCR_ISNULL_PSHARED:Decls->UPCR_ISNULL_SHARED, args);
	return SemaRef.CreateBuiltinUnaryOp(SourceLocation(), UO_LNot, Test.get());
      } else {
	return Result;
      }
    }

    Sema::ConditionResult TransformCondition(
      SourceLocation Loc, VarDecl *Var, Expr *Expr, Sema::ConditionKind Kind) {
      if (Var) {
        VarDecl *ConditionVar = cast_or_null<VarDecl>(
          getDerived().TransformDefinition(Var->getLocation(), Var));

        if (!ConditionVar)
          return Sema::ConditionError();

        return getSema().ActOnConditionVariable(ConditionVar, Loc, Kind);
      }

      if (Expr) {
        ExprResult CondExpr = TransformCondition(Expr);

        if (CondExpr.isInvalid())
          return Sema::ConditionError();

        return getSema().ActOnCondition(nullptr, Loc, CondExpr.get(), Kind);
      }

      return Sema::ConditionResult();
    }

    ExprResult TransformConditionalOperator(ConditionalOperator *E) {
      // The only difference from the default is this TransformCondition vs TransformExpr:
      ExprResult Cond = TransformCondition(E->getCond());
      if (Cond.isInvalid())
	return ExprError();

      ExprResult LHS = TransformExpr(E->getLHS());
      if (LHS.isInvalid())
	return ExprError();

      ExprResult RHS = TransformExpr(E->getRHS());
      if (RHS.isInvalid())
	return ExprError();

      return getDerived().RebuildConditionalOperator(Cond.get(), E->getQuestionLoc(), LHS.get(), E->getColonLoc(), RHS.get());
    }
    using TreeTransformUPC::TransformCompoundStmt;
    StmtResult TransformCompoundStmt(CompoundStmt *S,
				     bool IsStmtExpr) {
      Sema::CompoundScopeRAII CompoundScope(getSema());

      bool SubStmtInvalid = false;
      bool SubStmtChanged = false;
      SmallVector<Stmt*, 8> Statements;
      for (CompoundStmt::body_iterator B = S->body_begin(), BEnd = S->body_end();
	   B != BEnd; ++B) {
	StmtResult Result = TransformStmt(*B);
	if (Result.isInvalid()) {
	  // Immediately fail if this was a DeclStmt, since it's very
	  // likely that this will cause problems for future statements.
	  if (isa<DeclStmt>(*B))
	    return StmtError();

	  // Otherwise, just keep processing substatements and fail later.
	  SubStmtInvalid = true;
	  continue;
	}

	SubStmtChanged = SubStmtChanged || Result.get() != *B;

	// Insert extra statments first
	Statements.append(SplitDecls.begin(), SplitDecls.end());
	SplitDecls.clear();

	// Skip NullStmts.  Several transformations
	// can generate them, and they aren't needed.
	if(!Result.isInvalid() && isa<NullStmt>(Result.get()))
	  continue;

	Statements.push_back(Result.getAs<Stmt>());
      }

      if (SubStmtInvalid)
	return StmtError();

      if (!getDerived().AlwaysRebuild() &&
	  !SubStmtChanged)
	return S;

      return getDerived().RebuildCompoundStmt(S->getLBracLoc(),
					      Statements,
					      S->getRBracLoc(),
					      IsStmtExpr);
    }
    StmtResult TransformReturnStmt(ReturnStmt * S) {
      Expr * Result = S->getRetValue();
      if(Result)
	Result = TransformExpr(Result).get();
      SmallVector<Stmt*, 2> Statements;
      std::vector<Expr*> args;
      FunctionDecl * CurFunction = SemaRef.getCurFunctionDecl();
      QualType ResultType = CurFunction->getReturnType();
      if(ResultType->isVoidType() && Result) {
	// Just evaluate it
	Statements.push_back(Result);
	Result = NULL;
      }
      if(!ResultType->isVoidType() && Result) {
	VarDecl *D = CreateTmpVar(ResultType);
	Expr *V = CreateSimpleDeclRef(D);
	Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, V, Result).get());
	Result = V;
      }
      Statements.push_back(BuildUPCRCall(Decls->UPCR_EXIT_FUNCTION, args, S->getReturnLoc()).get());
      Statements.push_back(SemaRef.BuildReturnStmt(S->getReturnLoc(), Result).get());
      return SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
    }
    StmtResult TransformUPCPragmaStmt(UPCPragmaStmt *) {
      // #pragma upc should be stripped out
      return SemaRef.ActOnNullStmt(SourceLocation());
    }
    VarDecl *CreateTmpVar(QualType Ty) {
      int ID = static_cast<int>(LocalTemps.size());
      std::string name = (llvm::Twine("_bupc_spilld") + llvm::Twine(ID)).str();
      VarDecl *TmpVar = VarDecl::Create(SemaRef.Context, SemaRef.getFunctionLevelDeclContext(), SourceLocation(), SourceLocation(), &SemaRef.Context.Idents.get(name), Ty, SemaRef.Context.getTrivialTypeSourceInfo(Ty), SC_None);
      LocalTemps.push_back(TmpVar);
      return TmpVar;
    }
    // Creates a typedef for arrays and other types
    // that have parts after the identifier.  Modify
    // the types in place.
    void MakeTLDTypedef(QualType &Ty, TypeSourceInfo *&TyInfo) {
      CheckForArray check;
      check.TraverseType(Ty);
      if(check.Found) {
        TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(Ty);
        TranslationUnitDecl *TU = SemaRef.Context.getTranslationUnitDecl();
        std::string Name = (Twine("_cupc2c_tld") + Twine(AnonRecordID++)).str();
        TypedefDecl *NewTypedef = TypedefDecl::Create(SemaRef.Context, TU,
                                         SourceLocation(), SourceLocation(),
                                         &SemaRef.Context.Idents.get(Name),
                                         TSI);
        LocalStatics.push_back(NewTypedef);
        Ty = SemaRef.Context.getTypedefType(NewTypedef);
        TyInfo = SemaRef.Context.getTrivialTypeSourceInfo(Ty);
      }
    }
    // Allow decls to be skipped
    StmtResult TransformDeclStmt(DeclStmt *S) {
      SmallVector<Decl *, 4> Decls;
      for (DeclStmt::decl_iterator D = S->decl_begin(), DEnd = S->decl_end();
	   D != DEnd; ++D) {
	Decl *Transformed = TransformDefinition((*D)->getLocation(), *D);

	// Split shared struct S {} *value;
	// into shared struct S {}; upcr_pshared_ptr_t value;
	if (Transformed && Decls.size() == 1 &&
	    isa<TagDecl>(Decls[0]) &&
	    isPointerToShared(GetBaseType(getDeclType(Transformed))))
	{
	  SplitDecls.push_back(RebuildDeclStmt(Decls, S->getBeginLoc(), S->getEndLoc()).get());
	  Decls.clear();
	}
	
	if(Transformed)
	  Decls.push_back(Transformed);
      }
      
      if(Decls.empty()) {
	return SemaRef.ActOnNullStmt(S->getEndLoc());
      } else {
	return RebuildDeclStmt(Decls, S->getBeginLoc(), S->getEndLoc());
      }
    }
    Decl *TransformDecl(SourceLocation Loc, Decl *D) {
      if(D == NULL) return NULL;
      Decl *Result = TreeTransformUPC::TransformDecl(Loc, D);
      if(Result == D) {
	Result = TransformDeclaration(D, SemaRef.CurContext);
      }
      return Result;
    }
    //Decl *TransformDefinition(SourceLocation Loc, Decl *D) {
    //  return TransformDeclaration(D, SemaRef.CurContext);
    //}
    Decl *TransformDeclaration(Decl *D, DeclContext *DC) {
      Decl *Result = TransformDeclarationImpl(D, DC);
      if(Result) {
	if(D->isImplicit())
	  Result->setImplicit();
	transformedLocalDecl(D, Result);
      }
      return Result;
    }
    bool isPhaseless(QualType Pointee) {
      return Pointee.getQualifiers().getLayoutQualifier() <= 1 &&
	!Pointee->isVoidType();
    }
    QualType TransformQualifiedType(TypeLocBuilder &TLB, QualifiedTypeLoc T) {
      
      Qualifiers Quals = T.getType().getLocalQualifiers();

      QualType Result = getDerived().TransformType(TLB, T.getUnqualifiedLoc());
      if (Result.isNull())
	return QualType();

      // Silently suppress qualifiers if the result type can't be qualified.
      // FIXME: this is the right thing for template instantiation, but
      // probably not for other clients.
      if (Result->isFunctionType() || Result->isReferenceType())
	return Result;

      // Suppress restrict on pointers-to-shared
      if (Quals.hasRestrict() && (!Result->isPointerType() ||
				  Result->hasPointerToSharedRepresentation()))
	Quals.removeRestrict();

      if (!Quals.empty()) {
	Result = SemaRef.BuildQualifiedType(Result, T.getBeginLoc(), Quals);
	// BuildQualifiedType might not add qualifiers if they are invalid.
	if (Result.hasLocalQualifiers())
	  TLB.push<QualifiedTypeLoc>(Result);
	// No location information to preserve.
      }

      return Result;
    }
    QualType TransformPointerType(TypeLocBuilder &TLB, PointerTypeLoc TL) {
      if(isPointerToShared(TL.getType())) {
	QualType Result = isPhaseless(TL.getType()->getAs<PointerType>()->getPointeeType())?
	  Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	TypedefTypeLoc NewT = TLB.push<TypedefTypeLoc>(Result);
	NewT.setNameLoc(SourceLocation());
	return Result;
      } else {
	return TreeTransformUPC::TransformPointerType(TLB, TL);
      }
    }
    QualType TransformDecayedType(TypeLocBuilder &TLB, DecayedTypeLoc TL) {
      // For pointers to shared, we need to ignore the
      // fact that it was written as an array.
      if(isPointerToShared(TL.getType())) {
	QualType Result = isPhaseless(TL.getType()->getAs<PointerType>()->getPointeeType())?
	  Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t;
	TypedefTypeLoc NewT = TLB.push<TypedefTypeLoc>(Result);
	NewT.setNameLoc(SourceLocation());
	return Result;
      } else {
	return TreeTransformUPC::TransformDecayedType(TLB, TL);
      }
    }
    QualType TransformUPCThreadArrayType(TypeLocBuilder &TLB, UPCThreadArrayTypeLoc TL) {
      // Translate UPCThreadArrayType into a VariableArrayType
      const UPCThreadArrayType *T = TL.getTypePtr();
      QualType ElementType = getDerived().TransformType(TLB, TL.getElementLoc());
      if (ElementType.isNull())
	return QualType();

      QualType Result = TL.getType();

      Expr *Size = IntegerLiteral::Create(SemaRef.Context, T->getSize(), SemaRef.Context.getSizeType(), SourceLocation());
      if(T->getThread()) {
	std::vector<Expr*> args;
	Expr *Threads = BuildUPCRCall(Decls->upcr_threads, args).get();
	Size = MaybeAddParensForMultiply(Size);
	Size = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Mul, Size, Threads).get();
      }

      Result = RebuildVariableArrayType(ElementType,
					T->getSizeModifier(),
					Size,
					T->getIndexTypeCVRQualifiers(),
					TL.getBracketsRange());

      ArrayTypeLoc NewTL = TLB.push<ArrayTypeLoc>(Result);
      NewTL.setLBracketLoc(TL.getLBracketLoc());
      NewTL.setRBracketLoc(TL.getRBracketLoc());
      NewTL.setSizeExpr(Size);

      return Result;
    }

    // The original version of this in TreeTransform doesn't quite work
    // for us.
    ParmVarDecl *TransformFunctionTypeParam(
        ParmVarDecl *OldParm, int indexAdjustment,
        Optional<unsigned> NumExpansions,
        bool ExpectParameterPack) {
      TypeSourceInfo *OldDI = OldParm->getTypeSourceInfo();
      TypeSourceInfo *NewDI = nullptr;

      if (NumExpansions && isa<PackExpansionType>(OldDI->getType())) {
        // If we're substituting into a pack expansion type and we know the
        // length we want to expand to, just substitute for the pattern.
        TypeLoc OldTL = OldDI->getTypeLoc();
        PackExpansionTypeLoc OldExpansionTL = OldTL.castAs<PackExpansionTypeLoc>();

        TypeLocBuilder TLB;
        TypeLoc NewTL = OldDI->getTypeLoc();
        TLB.reserve(NewTL.getFullDataSize());

        QualType Result = getDerived().TransformType(TLB,
                                                     OldExpansionTL.getPatternLoc());
        if (Result.isNull())
          return nullptr;

        Result = RebuildPackExpansionType(Result,
                                          OldExpansionTL.getPatternLoc().getSourceRange(),
                                          OldExpansionTL.getEllipsisLoc(),
                                          NumExpansions);
        if (Result.isNull())
          return nullptr;

        PackExpansionTypeLoc NewExpansionTL
          = TLB.push<PackExpansionTypeLoc>(Result);
        NewExpansionTL.setEllipsisLoc(OldExpansionTL.getEllipsisLoc());
        NewDI = TLB.getTypeSourceInfo(SemaRef.Context, Result);
      } else
        NewDI = getDerived().TransformType(OldDI);
      if (!NewDI)
        return nullptr;

      if (NewDI == OldDI && indexAdjustment == 0)
        return OldParm;

      // The original DC is in the wrong ASTContext.  That's
      // fine for template instantiation, but it doesn't work
      // when we're creating an entirely new AST.
      DeclContext *NewDC = cast<DeclContext>(TransformDecl(SourceLocation(),
        cast<Decl>(OldParm->getDeclContext())));
      ParmVarDecl *newParm = ParmVarDecl::Create(SemaRef.Context,
                                                 NewDC,
                                                 OldParm->getInnerLocStart(),
                                                 OldParm->getLocation(),
                                                 OldParm->getIdentifier(),
                                                 NewDI->getType(),
                                                 NewDI,
                                                 OldParm->getStorageClass(),
                                                 /* DefArg */ nullptr);
      newParm->setScopeInfo(OldParm->getFunctionScopeDepth(),
                            OldParm->getFunctionScopeIndex() + indexAdjustment);
      return newParm;
    }
    // Transforms the type of a declaration by adding
    // typedefs for anonymous structs/unions
    TypedefDecl *MakeTypedefForAnonRecordImpl(QualType Element) {
      // If this was declared using an anonymous struct,
      // then we need to create a typedef, so that we
      // can refer to it later.
      if(const TagType *TT = dyn_cast<TagType>(Element.getTypePtr())) {
        if(!TT->getDecl()->getIdentifier()) {
	  TranslationUnitDecl *TU = SemaRef.Context.getTranslationUnitDecl();
          TypedefDecl *& NewTypedef = ExtraAnonTagDecls[TT->getDecl()];
          if(NewTypedef == NULL) {
            std::string Name = (Twine("_bupc_anon_struct") + Twine(AnonRecordID++)).str();
            NewTypedef = TypedefDecl::Create(SemaRef.Context, TU,
                                             SourceLocation(), SourceLocation(),
                                             &SemaRef.Context.Idents.get(Name),
                                             SemaRef.Context.getTrivialTypeSourceInfo(Element));
            LocalStatics.push_back(NewTypedef);
          }

          return NewTypedef;
        }
      }
      // Not an anonymous struct.
      return NULL;
    }
    QualType MakeTypedefForAnonRecord(QualType RealType) {
      QualType Element = SemaRef.Context.getBaseElementType(RealType);
      RecordDecl *RD = nullptr;

      if(const ElaboratedType * ET = dyn_cast<ElaboratedType>(Element)) {
        Element = ET->getNamedType();
        RD = ET->getAsRecordDecl();
      }
      if(TypedefDecl *NewTypedef = MakeTypedefForAnonRecordImpl(Element)) {
        // We set the original anonymous struct definition to the canonical decl and name
        // This allows the typedefs to correctly refer back to the original struct
        // and removes any explicit anonymity
        if( RD ){
          RD->setDeclName(NewTypedef->getCanonicalDecl()->getDeclName());
        }

        SubstituteType Sub(SemaRef, Element, SemaRef.Context.getTypedefType(NewTypedef));
        RealType = Sub.TransformType(RealType);
      }
      return RealType;
    }
    TypeSourceInfo *MakeTypedefForAnonRecord(TypeSourceInfo *RealType) {
      QualType Element = SemaRef.Context.getBaseElementType(RealType->getType());
      if(const ElaboratedType * ET = dyn_cast<ElaboratedType>(Element)) {
        Element = ET->getNamedType();
      }
      if(TypedefDecl *NewTypedef = MakeTypedefForAnonRecordImpl(Element)) {
        SubstituteType Sub(SemaRef, Element, SemaRef.Context.getTypedefType(NewTypedef));
        RealType = Sub.TransformType(RealType);
      }
      return RealType;
    }
    IdentifierInfo * mangleStaticLocalName(IdentifierInfo * VarName) {
      std::string Name = (llvm::Twine("_bupc_static_local") +
                          llvm::Twine(StaticLocalVarID++) + 
                          VarName->getName()).str();
      return &SemaRef.Context.Idents.get(Name);
    }
    IdentifierInfo * mangleLocalRecordName(IdentifierInfo * VarName) {
      std::string Name = (llvm::Twine("_bupc_local_decl") +
                          llvm::Twine(StaticLocalVarID++) + 
                          VarName->getName()).str();
      return &SemaRef.Context.Idents.get(Name);
    }
    Decl *TransformDeclarationImpl(Decl *D, DeclContext *DC) {
      if(isa<NamedDecl>(D) && cast<NamedDecl>(D)->getIdentifier() == &SemaRef.Context.Idents.get("__builtin_va_list")) {
	return SemaRef.Context.getBuiltinVaListDecl();
      } else if(TranslationUnitDecl *TUD = dyn_cast<TranslationUnitDecl>(D)) {
	return TransformTranslationUnitDecl(TUD);
      } else if(FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
	DeclarationNameInfo FnName = FD->getNameInfo();
	DeclarationName Name = FnName.getName();
	bool isMain = false;
	if(Name == &SemaRef.Context.Idents.get("main")) {
	  FnName.setName(&SemaRef.Context.Idents.get("user_main"));
	  isMain = true;
	} else if(Name == &SemaRef.Context.Idents.get("__builtin_va_start")) {
	  FnName.setName(&SemaRef.Context.Idents.get("va_start"));
	} else if(Name == &SemaRef.Context.Idents.get("__builtin_va_end")) {
	  FnName.setName(&SemaRef.Context.Idents.get("va_end"));
	} else if(Name == &SemaRef.Context.Idents.get("__builtin_va_copy")) {
	  FnName.setName(&SemaRef.Context.Idents.get("va_copy"));
	}

        // The TypeSourceInfo for the function cannot be
        // initialized correctly until the parameter declarations
        // have been processed.  getTrivialTypeSourceInfo
        // is good enough for our purposes.
	TypeSourceInfo * FTSI = FD->getTypeSourceInfo()? SemaRef.Context.getTrivialTypeSourceInfo(TransformType(FD->getType())) : 0;
	FunctionDecl *result = FunctionDecl::Create(SemaRef.Context, DC, FD->getBeginLoc(),
				    FnName, TransformType(FD->getType()),
				    FTSI,
				    FD->isInlineSpecified()?SC_Static:FD->getStorageClass(),
				    false, FD->hasWrittenPrototype(),
                                    FD->getConstexprKind());
				    //FD->isConstexpr());
	transformedLocalDecl(D, result);
        copyAttrs(D, result);
	// Copy the parameters
	SmallVector<ParmVarDecl *, 2> Parms;
	int i = 0;
	for(FunctionDecl::param_iterator iter = FD->param_begin(), end = FD->param_end(); iter != end; ++iter) {
	  ParmVarDecl *OldParam = *iter;
	  TypeSourceInfo *PTSI = OldParam->getTypeSourceInfo();
	  if(PTSI && PTSI->getType().getQualifiers().hasShared()) {
	    // Make sure that shared array parameters are decayed to pointers
	    PTSI = SemaRef.Context.getTrivialTypeSourceInfo(TransformType(SemaRef.Context.getAdjustedParameterType(PTSI->getType())));
	  } else {
	    PTSI = PTSI?TransformType(PTSI):0;
	  }
	  ParmVarDecl *Param = ParmVarDecl::Create(SemaRef.Context, result, OldParam->getBeginLoc(),
						   OldParam->getLocation(), OldParam->getIdentifier(),
						   TransformType(OldParam->getType()),
						   PTSI,
						   OldParam->getStorageClass(),
						   TransformExpr(OldParam->getDefaultArg()).get());
          copyAttrs(OldParam, Param);
	  Param->setScopeInfo(0, i++);
	  Parms.push_back(Param);
	}
	result->setParams(Parms);

	if(FD->doesThisDeclarationHaveABody()) {
	  SemaRef.ActOnStartOfFunctionDef(0, result);
	  Sema::SynthesizedFunctionScope Scope(SemaRef, result);
	  Stmt *FnBody;
	  {
	    Sema::CompoundScopeRAII BodyScope(SemaRef);
	    Stmt *UserBody = TransformStmt(FD->getBody()).get();
	    llvm::SmallVector<Stmt*, 8> Body;
	    {
	      std::vector<Expr*> args;
	      Body.push_back(BuildUPCRCall(Decls->UPCR_BEGIN_FUNCTION, args, UserBody->getBeginLoc()).get());
	    }
	    // Insert all the temporary variables that we created
	    for(std::vector<VarDecl*>::const_iterator iter = LocalTemps.begin(), end = LocalTemps.end(); iter != end; ++iter) {
	      Decl *decl_arr[] = { *iter };
	      Body.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, decl_arr, 1)), SourceLocation(), SourceLocation()).get());
	    }
	    LocalTemps.clear();
	    // Insert the user code
	    Body.push_back(UserBody);
	    {
	      std::vector<Expr*> args;
	      Body.push_back(BuildUPCRCall(Decls->UPCR_EXIT_FUNCTION, args, UserBody->getEndLoc()).get());
	    }
	    if(isMain)
	      Body.push_back(SemaRef.BuildReturnStmt(SourceLocation(), CreateInteger(SemaRef.Context.IntTy, 0)).get());
	    FnBody = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Body, false).get();
	  }
	  SemaRef.ActOnFinishFunctionBody(result, FnBody);
	}
	return result;
      } else if(VarDecl *VD = dyn_cast<VarDecl>(D)) {
	if(VD->getType().getQualifiers().hasShared()) {
	  TranslationUnitDecl *TU = SemaRef.Context.getTranslationUnitDecl();
	  QualType VarType = (isPhaseless(VD->getType())? Decls->upcr_pshared_ptr_t : Decls->upcr_shared_ptr_t );
          IdentifierInfo *VarName = VD->getIdentifier();
          if(VD->isStaticLocal()) {
            VarName = mangleStaticLocalName(VarName);
          }
	  VarDecl *result = VarDecl::Create(SemaRef.Context, TU, VD->getBeginLoc(),
					    VD->getLocation(), VarName,
					    VarType,
                                            SemaRef.Context.getTrivialTypeSourceInfo(VarType),
                                            VD->getStorageClass());
	  transformedLocalDecl(D, result);
          copyAttrs(D, result);
	  SharedGlobals.push_back(std::make_pair(result, VD));
	  Qualifiers Quals;
	  QualType RealType = TransformType(SemaRef.Context.getUnqualifiedArrayType(VD->getType(), Quals));
          RealType = MakeTypedefForAnonRecord(RealType);
	  if(Expr *Init = VD->getInit()) {
	    Qualifiers Quals;
	    SharedInitializers.push_back(std::make_pair(result, std::make_pair(TransformExpr(Init).get(), RealType)));
	  }
	  LocalStatics.push_back(result);
	  return NULL;
	} else if(needsDynamicInitializer(VD)) {
	  TranslationUnitDecl *TU = SemaRef.Context.getTranslationUnitDecl();
          QualType Ty = TransformType(VD->getType());
          TypeSourceInfo *TyInfo = TransformType(VD->getTypeSourceInfo());
          IdentifierInfo *VarName = VD->getIdentifier();
          if(isa<FunctionDecl>(VD->getDeclContext()) || shouldUseTLD(VD)) {
            Ty = MakeTypedefForAnonRecord(Ty);
            TyInfo = MakeTypedefForAnonRecord(TyInfo);
          }
          if(shouldUseTLD(VD)) {
            MakeTLDTypedef(Ty, TyInfo);
          }
          if(VD->isStaticLocal()) {
            VarName = mangleStaticLocalName(VarName);
          }
	  VarDecl *result = VarDecl::Create(SemaRef.Context, TU,
                                            VD->getBeginLoc(),
                                            VD->getLocation(),
                                            VarName, Ty,
                                            TyInfo,
					    VD->getStorageClass());
          if(shouldUseTLD(VD)) {
            ThreadLocalDecls.insert(result);
          }
	  transformedLocalDecl(D, result);
          copyAttrs(D, result);
	  Expr *Init = VD->getInit();
	  DynamicInitializers.push_back(std::make_pair(result, TransformExpr(Init).get()));
	  LocalStatics.push_back(result);
	  return NULL;
	} else {
          QualType Ty = TransformType(VD->getType());
          TypeSourceInfo *TyInfo = TransformType(VD->getTypeSourceInfo());
          DeclContext *NewDC = DC;
          IdentifierInfo *VarName = VD->getIdentifier();
          if(isa<FunctionDecl>(VD->getDeclContext()) || shouldUseTLD(VD)) {
            Ty = MakeTypedefForAnonRecord(Ty);
            TyInfo = MakeTypedefForAnonRecord(TyInfo);
          }
          if(shouldUseTLD(VD)) {
            MakeTLDTypedef(Ty, TyInfo);
            NewDC = SemaRef.Context.getTranslationUnitDecl();
            if(VD->isStaticLocal()) {
              VarName = mangleStaticLocalName(VarName);
            }
            NewDC = SemaRef.Context.getTranslationUnitDecl();
          }

	  VarDecl *result = VarDecl::Create(SemaRef.Context, NewDC,
                                            VD->getBeginLoc(),
                                            VD->getLocation(),
                                            VarName,
					    Ty, TyInfo,
					    VD->getStorageClass());
          if(shouldUseTLD(VD)) {
            ThreadLocalDecls.insert(result);
          }
	  transformedLocalDecl(D, result);
          copyAttrs(D, result);
	  if(Expr *Init = VD->getInit()) {
	    SemaRef.AddInitializerToDecl(result, TransformExpr(Init).get(), VD->isDirectInit());
	  }
          if(shouldUseTLD(VD)) {
            LocalStatics.push_back(result);
          } else {
            return result;
          }
	}
      } else if(RecordDecl *RD = dyn_cast<RecordDecl>(D)) {
	IdentifierInfo *Name = getRecordDeclName(RD->getIdentifier());
        TypedefNameDecl *TDND = RD->getTypedefNameForAnonDecl();
        DeclContext *NewDC = DC;
        // Mangle struct names that get promoted to the global scope
        if(Name && isa<FunctionDecl>(RD->getDeclContext())) {
          Name = mangleLocalRecordName(Name);
        }
        if(isa<FunctionDecl>(RD->getDeclContext())) {
          NewDC = SemaRef.Context.getTranslationUnitDecl();
        }
	RecordDecl *Result = RecordDecl::Create(SemaRef.Context, RD->getTagKind(), NewDC,
				  RD->getBeginLoc(), RD->getLocation(),
				  Name, cast_or_null<RecordDecl>(TransformDecl(SourceLocation(), RD->getPreviousDecl())));
        if(TDND){
          Result->setTypedefNameForAnonDecl(TDND);
          Result->setDeclName(TDND->getDeclName());
        }

	transformedLocalDecl(D, Result);
        copyAttrs(D, Result);
	SmallVector<Decl *, 4> Fields;
	if(RD->isThisDeclarationADefinition()) {
	  Result->startDefinition();
          Scope CurScope(SemaRef.getCurScope(), Scope::ClassScope|Scope::DeclScope, SemaRef.getDiagnostics());
          clang::Sema::ContextRAII SaveCtx(SemaRef, NewDC);
	  SemaRef.ActOnTagStartDefinition(&CurScope, Result);
	  for(RecordDecl::decl_iterator iter = RD->decls_begin(), end = RD->decls_end(); iter != end; ++iter) {
	    if(FieldDecl *FD = dyn_cast_or_null<FieldDecl>(*iter)) {

	      TypeSourceInfo *DI = FD->getTypeSourceInfo();
	      if(DI) DI = TransformType(DI);

	      FieldDecl *NewFD = SemaRef.CheckFieldDecl(FD->getDeclName(),
                                                        TransformType(FD->getType()),
                                                        DI,
                                                        Result,
                                                        FD->getLocation(),
                                                        FD->isMutable(),
                                                        TransformExpr(FD->getBitWidth()).get(),
                                                        FD->getInClassInitStyle(),
                                                        FD->getInnerLocStart(),
                                                        FD->getAccess(), 0);

	      transformedLocalDecl(FD, NewFD);
              copyAttrs(FD, NewFD);
	      NewFD->setImplicit(FD->isImplicit());
	      NewFD->setAccess(FD->getAccess());
	      Result->addDecl(NewFD);
	      Fields.push_back(NewFD);
	    } else if(IndirectFieldDecl *IFD = dyn_cast_or_null<IndirectFieldDecl>(*iter)) {
	      NamedDecl **Chaining = new(SemaRef.Context) NamedDecl*[IFD->getChainingSize()];
	      NamedDecl **OutIt = Chaining;
	      for(IndirectFieldDecl::chain_iterator chain_iter = IFD->chain_begin(), chain_end = IFD->chain_end(); chain_iter != chain_end; ++chain_iter, ++OutIt) {
		*OutIt = cast<NamedDecl>(TransformDecl(SourceLocation(), *chain_iter));
	      }
	      IndirectFieldDecl *NewIFD = IndirectFieldDecl::Create(SemaRef.Context, Result, IFD->getLocation(), IFD->getIdentifier(), TransformType(IFD->getType()), MutableArrayRef<NamedDecl *>(Chaining, IFD->getChainingSize()));
	      NewIFD->setImplicit(true);
	      transformedLocalDecl(IFD, NewIFD);
              copyAttrs(IFD, NewIFD);
	      Result->addDecl(NewIFD);
	    } else {
	      // Skip tag forward declarations.
	      // struct { shared struct A * ptr; }; used to
	      // be translated into struct { struct A; upc_pshared_ptr_t ptr; };
	      // These extra declarations are harmless elsewhere, but they
	      // cause warnings inside structs.
              if(TagDecl *TD = dyn_cast<TagDecl>(*iter))
		if(!TD->isThisDeclarationADefinition())
		  continue;
	      Result->addDecl(TransformDecl(SourceLocation(), *iter));
	    }
	  }
          // Create an empty attribute list
          ParsedAttributesView AttrList;
	  SemaRef.ActOnFields(0, Result->getLocation(), Result, Fields, SourceLocation(), SourceLocation(), AttrList);
	  SemaRef.ActOnTagFinishDefinition(&CurScope, Result, RD->getBraceRange());
	}
        if(isa<FunctionDecl>(RD->getDeclContext())) {
          // Promote local struct declarations to the global scope
          LocalStatics.push_back(Result);
          return NULL;
        } else {
          return Result;
        }
      } else if(TypedefDecl *TD = dyn_cast<TypedefDecl>(D)) {
	TypeSourceInfo *Ty;
	if(TD->getUnderlyingType().getQualifiers().hasShared()) {
	  return 0;
	} else {
	  Ty = TransformType(TD->getTypeSourceInfo());
	}
        IdentifierInfo *Name = TD->getIdentifier();
        DeclContext *NewDC = DC;
        CheckForLocalType Checker;
        Checker.TraverseType(TD->getUnderlyingType().getCanonicalType());
        if(!Checker.Found && isa<FunctionDecl>(TD->getDeclContext())) {
          Name = mangleLocalRecordName(Name);
          NewDC = SemaRef.Context.getTranslationUnitDecl();
        }
	TypedefDecl *Result = TypedefDecl::Create(SemaRef.Context, NewDC, TD->getBeginLoc(), TD->getLocation(), Name, Ty);
        copyAttrs(D, Result);

        if(TD->isModed()) {
          Result->setModedTypeSourceInfo(Ty, TransformType(TD->getUnderlyingType()));
        }
        transformedLocalDecl(TD, Result);
        if(!Checker.Found && isa<FunctionDecl>(TD->getDeclContext())) {
          // Typedefs are always promoted to the global scope
          // when it's safe to do so.
          LocalStatics.push_back(Result);
          return NULL;
        } else {
          return Result;
        }
      } else if(EnumDecl *ED = dyn_cast<EnumDecl>(D)) {
        TypedefNameDecl *TDND = ED->getTypedefNameForAnonDecl();
	EnumDecl * PrevDecl = 0;
	if(EnumDecl * OrigPrevDecl = ED->getPreviousDecl()) {
	  PrevDecl = cast<EnumDecl>(TransformDecl(SourceLocation(), OrigPrevDecl));
	}

	EnumDecl *Result = EnumDecl::Create(SemaRef.Context, DC, ED->getBeginLoc(), ED->getLocation(),
					    ED->getIdentifier(), PrevDecl, ED->isScoped(),
					    ED->isScopedUsingClassTag(), ED->isFixed());
        if(TDND){
          Result->setTypedefNameForAnonDecl(TDND);
          Result->setDeclName(TDND->getDeclName());
        }
	transformedLocalDecl(D, Result);
        copyAttrs(D, Result);

	if(ED->isThisDeclarationADefinition()) {
	  Result->startDefinition();

	  SmallVector<Decl *, 4> Enumerators;

	  EnumConstantDecl *PrevEnumConstant = 0;
	  for(EnumDecl::enumerator_iterator iter = ED->enumerator_begin(), end = ED->enumerator_end(); iter != end; ++iter) {
	    Expr *Value = 0;
	    if(Expr *OrigValue = iter->getInitExpr()) {
	      Value = TransformExpr(OrigValue).get();
	    }
	    EnumConstantDecl *EnumConstant = SemaRef.CheckEnumConstant(Result, PrevEnumConstant, iter->getLocation(), iter->getIdentifier(), Value);
	    transformedLocalDecl(*iter, EnumConstant);
            copyAttrs(*iter, EnumConstant);

	    EnumConstant->setAccess(Result->getAccess());
	    Result->addDecl(EnumConstant);
	    Enumerators.push_back(EnumConstant);
	    PrevEnumConstant = EnumConstant;

	  }

          // Create an empty attribute list
          ParsedAttributesView AttrList;
	  SemaRef.ActOnEnumBody(Result->getLocation(), Result->getBraceRange(), Result, Enumerators, nullptr, AttrList);
	}

	return Result;
      } else if(LabelDecl *LD = dyn_cast<LabelDecl>(D)) {
	LabelDecl *Result;
	if(LD->isGnuLocal()) {
	  Result = LabelDecl::Create(SemaRef.Context, DC, LD->getLocation(), LD->getIdentifier(), LD->getBeginLoc());
	} else {
	  Result = LabelDecl::Create(SemaRef.Context, DC, LD->getLocation(), LD->getIdentifier());
	}
        copyAttrs(D, Result);
	// FIXME: What to do about the statement?
        return Result;
      } else if(isa<EmptyDecl>(D)) {
	return EmptyDecl::Create(SemaRef.Context, DC, D->getLocation());
      } else if(PragmaPupcDecl *PD = dyn_cast<PragmaPupcDecl>(D)) {
        return PragmaPupcDecl::Create(SemaRef.Context, DC, PD->getLocation(), PD->getOn());
      } else if(StaticAssertDecl *SAD = dyn_cast<StaticAssertDecl>(D)) {
        ExprResult E = TransformExpr(SAD->getAssertExpr());
        StringLiteral *Message = cast<StringLiteral>(TransformExpr(SAD->getMessage()).get());
        return StaticAssertDecl::Create(SemaRef.Context, DC, SAD->getLocation(),
                                        E.get(), Message, SAD->getRParenLoc(),
                                        SAD->isFailed());
      } else {
	assert(!"Unknown Decl");
      }
      // Should not get here
      return NULL;
    }
    void copyAttrs(Decl * src, Decl *dst) {
      for(Decl::attr_iterator iter = src->attr_begin(), end = src->attr_end();
          iter != end; ++iter) {
        dst->addAttr((*iter)->clone(SemaRef.Context));
      }
    }
    std::set<StringRef> CollectedIncludes;
    void PrintIncludes(llvm::raw_ostream& OS) {
      for(std::set<StringRef>::iterator iter = CollectedIncludes.begin(), end = CollectedIncludes.end(); iter != end; ++iter) {
	StringRef relativeFilePath = *iter;
	// Test successively larger paths until we
	// find where the header comes from.
	for(StringRef Parent = *iter; !Parent.empty(); Parent = llvm::sys::path::parent_path(Parent)) {
	  const char * start = llvm::sys::path::filename(Parent).begin();
	  StringRef TestFile = StringRef(start, iter->end() - start);
	  const DirectoryLookup *CurDir = NULL;
          bool IsMapped = false;
          bool IsFrameworkFound = false;
	  const FileEntry *found = SemaRef.PP.getHeaderSearchInfo().LookupFile(TestFile, SourceLocation(),
                                                                               true, NULL, CurDir, llvm::None,
                                                                               NULL, NULL, NULL, NULL,
                                                                               &IsMapped,&IsFrameworkFound);
	  if(found) {
	    if(found == SemaRef.SourceMgr.getFileManager().getFile(*iter)) {
	      relativeFilePath = TestFile;
	      break;
	    }
	  }
	}
	// Check whether this header has a special name
	std::map<StringRef, StringRef>::const_iterator pos = UPCHeaderRenames.find(relativeFilePath);
	if(pos != UPCHeaderRenames.end())
	  relativeFilePath = pos->second;
	OS << "#include <" << relativeFilePath << ">\n";
      }
    }
    bool TreatAsCHeader(SourceLocation Loc) {
      if(Loc.isInvalid()) return false;
      SourceManager& SrcManager = SemaRef.Context.getSourceManager();
      if(SrcManager.getFileID(Loc) == SrcManager.getMainFileID()) return false;
      // Make sure we don't output any UPC system includes
      std::string FilePath = SrcManager.getFilename(Loc).str();
      return FilePath.find("/upcr_preinclude/") == std::string::npos &&
	SrcManager.isInSystemHeader(Loc);
    }
    std::set<StringRef> UPCSystemHeaders;
    std::map<StringRef, StringRef> UPCHeaderRenames;
    Decl *TransformTranslationUnitDecl(TranslationUnitDecl *D) {
      TranslationUnitDecl *result = SemaRef.Context.getTranslationUnitDecl();
      transformedLocalDecl(D, result);
      Scope CurScope(0, Scope::DeclScope, SemaRef.getDiagnostics());
      SemaRef.setCurScope(&CurScope);
      SemaRef.PushDeclContext(&CurScope, result);

      // Process all Decls
      for(DeclContext::decl_iterator iter = D->decls_begin(),
          end = D->decls_end(); iter != end; ++iter) {
	Decl *decl = TransformDeclaration(*iter, result);
	SourceManager& SrcManager = SemaRef.Context.getSourceManager();
	SourceLocation Loc = SrcManager.getExpansionLoc((*iter)->getLocation());

	// Don't output Decls declared in system headers
	if(Loc.isInvalid() || !SrcManager.isInSystemHeader(Loc)) {
	  for(std::vector<Decl*>::const_iterator locals_iter = LocalStatics.begin(), locals_end = LocalStatics.end(); locals_iter != locals_end; ++locals_iter) {
	    if(!(*locals_iter)->isImplicit())
	      result->addDecl(*locals_iter);
	  }
	  if(decl && !decl->isImplicit())
	    result->addDecl(decl);
        } else {
	  if(TreatAsCHeader(Loc)) {
	    // Record the system headers included by user code
	    SourceLocation HeaderLoc;
	    SourceLocation IncludeLoc = Loc;
	    do {
	      HeaderLoc = IncludeLoc;
	      IncludeLoc = SrcManager.getIncludeLoc(SrcManager.getFileID(HeaderLoc));
	    } while(TreatAsCHeader(IncludeLoc));

	    StringRef Name = SrcManager.getFilename(HeaderLoc);
	    if(!Name.empty()) {
	      CollectedIncludes.insert(Name);
	    }
          }
	}
	LocalStatics.clear();
      }

      if(FunctionDecl *Alloc = GetSharedAllocationFunction()) {
	result->addDecl(Alloc);
      }
      if(FunctionDecl *Init = GetSharedInitializationFunction()) {
	result->addDecl(Init);
      }
      SemaRef.setCurScope(0);
      return result;
    }
    bool shouldUseTLD(VarDecl *D) {
      if (!SemaRef.Context.getLangOpts().UPCTLDEnable) return false;
      if(!D->hasGlobalStorage()) return false;
      SourceManager& SrcManager = SemaRef.Context.getSourceManager();
      SourceLocation Loc = SrcManager.getExpansionLoc(D->getLocation());
      return Loc.isInvalid() || !SrcManager.isInSystemHeader(Loc);
    }
    bool isUPCThreadLocal(Decl *D) {
      return ThreadLocalDecls.find(D) != ThreadLocalDecls.end();
    }
    std::set<Decl*> ThreadLocalDecls;
    std::map<Decl*, TypedefDecl*> ExtraAnonTagDecls;
    std::vector<Stmt*> SplitDecls;
    std::vector<Decl*> LocalStatics;
    UPCRDecls *Decls;
    std::string FileString;
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
      FunctionDecl *Result = Decls->CreateFunction(SemaRef.Context, "UPCRI_ALLOC_" + FileString, SemaRef.Context.VoidTy, 0, 0);
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
	  //args.push_back(SemaRef.BuildDeclRefExpr(iter->first, iter->first->getType(), VK_LValue, SourceLocation()).get());
	  //args.push_back(dynamic_cast<Expr *>(SemaRef.BuildDeclRefExpr(iter->first, iter->first->getType(), VK_LValue, SourceLocation())));
	  args.push_back(dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(iter->first, iter->first->getType(), VK_LValue, SourceLocation())));
	  uint32_t LayoutQualifier = iter->second->getType().getQualifiers().getLayoutQualifier();
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
	  llvm::APInt ElementSize(SizeTypeSize, SemaRef.Context.getTypeSizeInChars(ElemTy).getQuantity());
	  llvm::APInt ElementsInBlock = LayoutQualifier == 0? ArrayDimension : llvm::APInt(SizeTypeSize, LayoutQualifier);
	  llvm::APInt BlockSize = ElementsInBlock * ElementSize;
	  llvm::APInt NumBlocks = LayoutQualifier == 0?
	    llvm::APInt(SizeTypeSize, 1) :
	    (ArrayDimension + LayoutQualifier - 1).udiv(ElementsInBlock);
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, BlockSize, SemaRef.Context.getSizeType(), SourceLocation()));
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, NumBlocks, SemaRef.Context.getSizeType(), SourceLocation()));
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, hasThread), SemaRef.Context.getSizeType(), SourceLocation()));
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, ElementSize, SemaRef.Context.getSizeType(), SourceLocation()));
	  // FIXME: encode the correct mangled type
          const char MangledType[] = "";
	  args.push_back(StringLiteral::Create(SemaRef.Context, "", StringLiteral::Ascii, false, SemaRef.Context.getConstantArrayType(SemaRef.Context.getConstType(SemaRef.Context.CharTy), llvm::APInt(64, sizeof(MangledType)), ArrayType::Normal, 0), SourceLocation()));
	  if(Phaseless) {
	    PInitializers.push_back(BuildUPCRCall(Decls->UPCRT_STARTUP_PSHALLOC, args).get());
	  } else {
	    Initializers.push_back(BuildUPCRCall(Decls->UPCRT_STARTUP_SHALLOC, args).get());
	  }
	}
	VarDecl *_bupc_info;
	VarDecl *_bupc_pinfo;
	if(!Initializers.empty()) {
	  _bupc_info = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(),
						 &SemaRef.Context.Idents.get("_bupc_info"), _bupc_info_type, SemaRef.Context.getTrivialTypeSourceInfo(_bupc_info_type), SC_None);
	  // InitializerList semantics vary depending on whether the SourceLocations are valid.
	  SemaRef.AddInitializerToDecl(_bupc_info, SemaRef.ActOnInitList(Decls->FakeLocation, Initializers, Decls->FakeLocation).get(), false);
	  Decl *_bupc_info_arr[] = { _bupc_info };
	  Statements.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, _bupc_info_arr, 1)), SourceLocation(), SourceLocation()).get());
	}
	if(!PInitializers.empty()) {
	  _bupc_pinfo = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(),
						 &SemaRef.Context.Idents.get("_bupc_pinfo"), _bupc_pinfo_type, SemaRef.Context.getTrivialTypeSourceInfo(_bupc_pinfo_type), SC_None);
	  // InitializerList semantics vary depending on whether the SourceLocations are valid.
	  SemaRef.AddInitializerToDecl(_bupc_pinfo, SemaRef.ActOnInitList(Decls->FakeLocation, PInitializers, Decls->FakeLocation).get(), false);
	  Decl *_bupc_pinfo_arr[] = { _bupc_pinfo };
	  Statements.push_back(SemaRef.ActOnDeclStmt(Sema::DeclGroupPtrTy::make(DeclGroupRef::Create(SemaRef.Context, _bupc_pinfo_arr, 1)), SourceLocation(), SourceLocation()).get());
	}
	if(!Initializers.empty()) {
	  std::vector<Expr*> args;
	  //args.push_back(SemaRef.BuildDeclRefExpr(_bupc_info, _bupc_info_type, VK_LValue, SourceLocation()).get());
	  //args.push_back(dynamic_cast<Expr *>(SemaRef.BuildDeclRefExpr(_bupc_info, _bupc_info_type, VK_LValue, SourceLocation())));
	  args.push_back(dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(_bupc_info, _bupc_info_type, VK_LValue, SourceLocation())));
	  args.push_back(IntegerLiteral::Create(SemaRef.Context, llvm::APInt(SizeTypeSize, Initializers.size()), SemaRef.Context.getSizeType(), SourceLocation()));
	  Statements.push_back(BuildUPCRCall(Decls->upcr_startup_shalloc, args).get());
	}
	if(!PInitializers.empty()) {
	  std::vector<Expr*> args;
	  //args.push_back(SemaRef.BuildDeclRefExpr(_bupc_pinfo, _bupc_pinfo_type, VK_LValue, SourceLocation()).get());
	  //args.push_back(dynamic_cast<Expr *>(SemaRef.BuildDeclRefExpr(_bupc_pinfo, _bupc_pinfo_type, VK_LValue, SourceLocation())));
	  args.push_back(dyn_cast<Expr>(SemaRef.BuildDeclRefExpr(_bupc_pinfo, _bupc_pinfo_type, VK_LValue, SourceLocation())));
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

    bool needsDynamicInitializer(VarDecl *VD) {
      if(VD->hasGlobalStorage() && VD->hasInit()) {
        CheckForDynamicInitializer Check;
        Check.TraverseStmt(VD->getInit());
	return Check.Found;
      } else {
	return false;
      }
    }

    typedef std::vector<std::pair<VarDecl *, Expr *> > DynamicInitializersType;
    DynamicInitializersType DynamicInitializers;
    typedef std::vector<std::pair<VarDecl *, std::pair<Expr *, QualType> > > SharedInitializersType;
    SharedInitializersType SharedInitializers;
    FunctionDecl * GetSharedInitializationFunction() {
      FunctionDecl *Result = Decls->CreateFunction(SemaRef.Context, "UPCRI_INIT_" + FileString, SemaRef.Context.VoidTy, 0, 0);
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
	
	Expr *Cond_;
	{
	  std::vector<Expr*> args;
	  Expr *mythread = BuildUPCRCall(Decls->upcr_mythread, args).get();
	  Cond_ = SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_EQ, mythread, CreateInteger(SemaRef.Context.IntTy, 0)).get();
	}
        Sema::ConditionResult Cond = SemaRef.ActOnCondition(nullptr, SourceLocation(), Cond_, Sema::ConditionKind::Boolean);

	std::vector<VarDecl *> Initializers;
	for(SharedInitializersType::iterator iter = SharedInitializers.begin(), end = SharedInitializers.end(); iter != end; ++iter) {
	  std::string VarName = (Twine("_bupc_") + iter->first->getIdentifier()->getName() + "_val").str();
	  VarDecl *StoredInit = VarDecl::Create(SemaRef.Context, Result, SourceLocation(), SourceLocation(), &SemaRef.Context.Idents.get(VarName),
						iter->second.second, SemaRef.Context.getTrivialTypeSourceInfo(iter->second.second),
						SC_None);
	  StoredInit->setInit(iter->second.first);
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
	    PutOnce.push_back(BuildUPCRCall(Decls->UPCR_PUT(Phaseless), args).get());
	  }
	  Statements.push_back(SemaRef.ActOnIfStmt(SourceLocation(), false, nullptr, Cond, SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), PutOnce, false).get(), SourceLocation(), nullptr).get());
	}
	{
	  for(std::size_t i = 0; i < DynamicInitializers.size(); ++i) {
	    VarDecl * VD = DynamicInitializers[i].first;
	    Expr *LHS = CreateSimpleDeclRef(VD);
	    Expr *RHS = DynamicInitializers[i].second;
	    if(shouldUseTLD(VD))
	      LHS = BuildTLDRefExpr(dyn_cast<DeclRefExpr>(LHS)).get();
	    Statements.push_back(SemaRef.CreateBuiltinBinOp(SourceLocation(), BO_Assign, LHS, RHS).get());
	  }
	}

	Body = SemaRef.ActOnCompoundStmt(SourceLocation(), SourceLocation(), Statements, false);
      }
      SemaRef.ActOnFinishFunctionBody(Result, Body.get());
      return Result;
    }
  };

  class UPCPrintHelper : public clang::PrinterHelper {
  public:
    UPCPrintHelper(RemoveUPCTransform &T)
      : Trans(T) {}
    virtual bool handledStmt(Stmt *, raw_ostream &) { return false; }
    virtual bool handledDecl(Decl *D, PrintingPolicy const& Policy,
                             raw_ostream & OS) {
      if(VarDecl * VD = dyn_cast<VarDecl>(D)) {
        if(Trans.isUPCThreadLocal(VD) && !VD->hasExternalStorage()) {
          VD->getType().print(OS, Policy);
          OS << " UPCR_TLD_DEFINE(" << VD->getIdentifier()->getName() << ", "
             << Trans.getSema().Context.getTypeSizeInChars(VD->getType()).getQuantity() << ", " << Trans.getSema().Context.getTypeAlignInChars(VD->getType()).getQuantity() << ")";
          if(Expr * Init = VD->getInit()) {
            OS << " = ";
            Init->printPretty(OS, this, Policy);
          }
          return true;
        }
      }
      return false;
    }
    RemoveUPCTransform &Trans;
  };

  class RemoveUPCConsumer : public clang::SemaConsumer {
  public:
    RemoveUPCConsumer(StringRef Output, StringRef FileString, bool Lines) : filename(Output), fileid(FileString), lines(Lines) {}
    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
      if(Context.getDiagnostics().hasUncompilableErrorOccurred())
	return;

      TranslationUnitDecl *top = Context.getTranslationUnitDecl();
      // Copy the ASTContext and Sema
      LangOptions LangOpts = Context.getLangOpts();
      ASTContext newContext(LangOpts, Context.getSourceManager(),
			    Context.Idents, Context.Selectors, Context.BuiltinInfo);
      newContext.InitBuiltinTypes(Context.getTargetInfo());
      newContext.getDiagnostics().setIgnoreAllWarnings(true);
      ASTConsumer nullConsumer;
      UPCRDecls Decls(newContext);
      Sema newSema(S->getPreprocessor(), newContext, nullConsumer);
      RemoveUPCTransform Trans(newSema, &Decls, fileid);
      Decl *Result = Trans.TransformTranslationUnitDecl(top);
      std::error_code error;
      llvm::raw_fd_ostream OS(filename.c_str(), error, llvm::sys::fs::F_None);
      OS << "#include <upcr.h>\n";

      Trans.PrintIncludes(OS);

      OS << "#ifndef UPCR_TRANS_EXTRA_INCL\n"
	"#define UPCR_TRANS_EXTRA_INCL\n";
      if (Trans.HaveVAArg()) { // subclass of Expr - cannot be renamed directly
        OS <<
	  "#ifndef __builtin_va_arg\n"
	  "#define __builtin_va_arg(_a1,_a2) va_arg(_a1,_a2)\n"
	  "#endif\n";
      }
      if (Trans.HaveOffsetOf()) { // subclass of Expr - cannot be renamed directly
        OS <<
	  "#ifndef __builtin_offsetof\n"
	  "#define __builtin_offsetof(_a1,_a2) offsetof(_a1,_a2)\n"
	  "#endif\n";
      }
      if (LangOpts.UPCTLDEnable)
        OS <<
	  "int32_t UPCR_TLD_DEFINE_TENTATIVE(upcrt_forall_control, 4, 4);\n";
      else
        OS <<
	  "int32_t upcrt_forall_control;\n";
      OS <<
	"#define UPCRT_STARTUP_SHALLOC(sptr, blockbytes, numblocks, mult_by_threads, elemsz, typestr) \\\n"
	"      { &(sptr), (blockbytes), (numblocks), (mult_by_threads), (elemsz), #sptr, (typestr) }\n"
	"#define UPCRT_STARTUP_PSHALLOC UPCRT_STARTUP_SHALLOC\n"
	"#endif\n";

      PrintingPolicy Policy = newContext.getPrintingPolicy();
      //
      // Adjust the printing policy to NOT print the source location for
      // anonymous tags.  In Clang 9.0.1, this is true by default
      //
      Policy.AnonymousTagLocations = false;
      UPCPrintHelper helper(Trans);
      Policy.IncludeLineDirectives = lines;
      Policy.SM = &newContext.getSourceManager();
      Policy.Helper = &helper;
      Result->print(OS, Policy);
    }
    void InitializeSema(Sema& SemaRef) { S = &SemaRef; }
    void ForgetSema() { S = 0; }
  private:
    Sema *S;
    std::string filename;
    std::string fileid;
    bool lines;
  };

  class RemoveUPCAction : public clang::ASTFrontendAction {
  public:
    RemoveUPCAction(StringRef OutputFile, StringRef FileString, bool Lines) : filename(OutputFile), fileid(FileString), lines(Lines) {}
    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
      return std::unique_ptr<ASTConsumer>(new RemoveUPCConsumer(filename, fileid, lines));
    }
    std::string filename;
    std::string fileid;
    bool lines;
  };

}

int main(int argc, const char ** argv) {
  using namespace llvm::opt;
  using namespace clang::driver;

  // Parse the arguments
  std::unique_ptr<OptTable> Opts(createDriverOptTable());
  unsigned MissingArgIndex, MissingArgCount;
  const unsigned IncludedFlagsBitmask = options::CC1Option;
  InputArgList Args(
      Opts->ParseArgs(llvm::makeArrayRef(argv, argc),
                      MissingArgIndex, MissingArgCount, IncludedFlagsBitmask));

  // Read the input and output files and adjust the arguments
  std::string InputFile = Args.getLastArgValue(options::OPT_INPUT);
  std::string DefaultOutputFile = (llvm::sys::path::stem(InputFile) + ".trans.c").str();
  std::string OutputFile = Args.getLastArgValue(options::OPT_o, DefaultOutputFile);
  Args.eraseArg(options::OPT_o);

  bool Lines = !Args.hasArg(options::OPT_P);
  Args.eraseArg(options::OPT_P);

  // Write the arguments to a vector
  ArgStringList NewOptions;

  for(auto iter = Args.begin(), end = Args.end(); iter != end; ++iter) {
    // Always parse as UPC
    if((*iter)->getOption().getID() == options::OPT_INPUT &&
       iter != Args.begin()) {
      NewOptions.push_back("-xupc");
    }
    (*iter)->renderAsInput(Args, NewOptions);
  }
  // Disable CodeGen
  NewOptions.push_back("-fsyntax-only");

  // convert to std::string
  std::vector<std::string> options(NewOptions.begin(), NewOptions.end());

  FileManager * Files(new FileManager(FileSystemOptions()));
  ToolInvocation tool(options, new RemoveUPCAction(OutputFile, get_file_id(InputFile), Lines), Files);
  if(tool.run()) {
    return EXIT_SUCCESS;
  } else {
    return EXIT_FAILURE;
  }
}
