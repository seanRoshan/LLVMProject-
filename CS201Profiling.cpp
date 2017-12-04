/*
 * Authors: AmirAli Abdolrashidi 		<aabdo001@ucr.edu>
 * 			Shahriar Valielahi Roshan 	<svali003@ucr.edu>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"

#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Dominators.h"
 
using namespace llvm;
 
namespace {
	static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
		std::vector<Type*> printf_arg_types;
		printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
		 
		FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
		Function *func = mod->getFunction("printf");
		if(!func)
		func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
		func->setCallingConv(CallingConv::C);
		return func;
	}
	struct CS201Profiling : public FunctionPass {
		static char ID;
		LLVMContext *Context;
		CS201Profiling() : FunctionPass(ID) {}
		//Strings
		GlobalVariable *BasicBlockPrintfFormatStr = NULL;
		GlobalVariable *BasicBlockPrintfFormatStr2 = NULL;
		
		//Callback function for "printf()"
		Function *printf_func = NULL;
		//Global Variables
		std::map<std::string,GlobalVariable*> Counters;
		std::map<std::string,GlobalVariable*> EdgeCounters;	
		GlobalVariable* lastIndex;
		GlobalVariable* currentIndex;
		//The rest
		Value* EdgeFreqArray; //Local Dynamic Array
		std::map<std::string,std::vector<std::string>> LoopSet;//Names For All Loops
		std::vector<BasicBlock*> backEdgesSet;	//All back edges
		int nodeNum=0;	//Number of nodes

		
		 
		//----------------------------------
		bool doInitialization(Module &M) {
			errs() << "\n---------Starting CS201Profiling---------\n";
			Context = &M.getContext();
			lastIndex = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "lastIndex");
			currentIndex = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "currentIndex");
			const char *finalPrintString = "%s";
			const char *finalPrintString2 = ":\t%d\n";
			Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
			Constant *format_const2 = ConstantDataArray::getString(*Context, finalPrintString2);
			BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
			BasicBlockPrintfFormatStr2 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString2)+1), true, llvm::GlobalValue::PrivateLinkage, format_const2, "BasicBlockPrintfFormatStr2");

			printf_func = printf_prototype(*Context, &M);
			
			//CAKE: Give the basic blocks names!
			for(auto &F: M)
			{
				for(auto &BB: F)
				{
					std::string NodeName="BLOCK";
					NodeName+=std::to_string(nodeNum);
					nodeNum++;
					BB.setName(NodeName);	
					//CAKE: Initialize BB Counters
					std::string CounterName="Counter_"+BB.getName().str();
					Counters[BB.getName()]=new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), CounterName);
				}
			}
			//CAKE: Initialize Edge Counters
			for(auto &F: M)
			{
				for(auto &BB: F)
				{

					TerminatorInst *Term = BB.getTerminator();
					unsigned numSuccessor = Term->getNumSuccessors();
					for(unsigned i=0;i<numSuccessor;i++)
					{
						std::string EdgeCounterName="EdgeCounter_";
						std::string EdgeKey=BB.getName().str()+Term->getSuccessor(i)->getName().str();
						EdgeCounterName+=EdgeKey;
						//
						EdgeCounters[EdgeKey]=new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), EdgeCounterName);
					}
				}
			}

			errs() << "Module: " << M.getName() << "\n";
			 
			return true;
		}
		 
		//----------------------------------
		bool doFinalization(Module &M) {
			errs() << "-------Finished CS201Profiling----------\n";
			 
			return false;
		}
		//----------------------------------
		bool runOnFunction(Function &F) override {
			errs() << "Function: " << F.getName() << '\n';
			//CAKE: Put the edge array allocation in the very beginning
			int arraySize=nodeNum*nodeNum;
			IRBuilder<> builder(F.front().getFirstInsertionPt());
			//Define local dynamic array
			EdgeFreqArray = builder.CreateAlloca(IntegerType::get(getGlobalContext(), 32), ConstantInt::get(IntegerType::get(getGlobalContext(), 32), arraySize)); 
			Value *iter=builder.CreateGEP(EdgeFreqArray,ConstantInt::get(Type::getInt32Ty(*Context), 0));
			for(int i=0;i<arraySize;i++)	//EdgeFreqArray[]={0};
			{

				builder.CreateStore(ConstantInt::get(Type::getInt32Ty(*Context), 0), iter);
				iter=builder.CreateGEP(iter,ConstantInt::get(Type::getInt32Ty(*Context), 1));
			}

			builder.CreateStore(ConstantInt::get(Type::getInt32Ty(*Context), 0), lastIndex);	//lastIndex=0

			/////////////////
			//CAKE: Dominator sets calculated (and back edges)
			std::vector<BasicBlock*> backEdges;

			DominatorTree DT;
			DT.recalculate(F);

			errs() << "\n*************************\nDominator Sets: \n";
			for(auto &BB: F)
			{
			//CAKE: Vector for the dominator set
				std::vector<BasicBlock*> domSet;
				domSet.empty();
				errs()<<BB.getName()<<":\t";
				for(auto &BB2: F)
				{
				if(DT.dominates(&BB2,&BB)) 
					{
					errs()<<BB2.getName()<<" ";
					domSet.push_back(&BB2);//Push it into vector for future processing (loop)
					}
				}
				//errs()<<"\nWhat ";
				//for(auto k=0;k<domSet.size();k++)
				//	errs()<<domSet[k]->getName()<<" ";

				  TerminatorInst *Term = BB.getTerminator();
				  unsigned numSuccessor = Term->getNumSuccessors();
				errs()<<"| #SUCCESSORS: "<<numSuccessor<<": ";
				//Who are the successors?
				for(unsigned i=0;i<numSuccessor;i++)
				{
				errs()<< Term->getSuccessor(i)->getName()<<" ";

				//Back edge
				for(unsigned j=0;j<domSet.size();j++)
					if(Term->getSuccessor(i)==domSet[j]) 
					{
						errs()<<"(B)";
						backEdges.push_back(&BB);
						backEdges.push_back(domSet[j]);
						backEdgesSet.push_back(&BB);
						backEdgesSet.push_back(domSet[j]);
					}
				}
				errs()<<'\n';
			}
			//////
			//CAKE: Find loops: If a node's successor dominates it, it's a back edge. This means loop!
			errs()<<"*************************\nBack Edges Found:\t";


			for(auto i=backEdges.begin();i!=backEdges.end();i+=2)
			{
				std::vector<BasicBlock*> loop;

				BasicBlock* head=*i;
				BasicBlock* tail=*(i+1);
				std::string EdgeKey=head->getName().str()+tail->getName().str();

				errs()<<head->getName()<<"->"<<tail->getName();
				//Loop
				loop.push_back(tail);
			//errs()<<"\nTail ("<<tail->getName()<<") is pushed into loop.\n";
				LoopSet[EdgeKey].push_back(tail->getName().str());

				loop.push_back(head);
			//errs()<<"\nHead ("<<head->getName()<<") is pushed into loop.\n";	
				LoopSet[EdgeKey].push_back(head->getName().str());

				std::vector<BasicBlock*> stack;
				stack.push_back(head);

				while(stack.size()!=0)
				{
					BasicBlock* temp;
					temp=stack[0];
					stack.pop_back();
					//
					for( auto j = pred_begin(temp);j != pred_end(temp);j++)	//CAKE: WRITE THE PREDECESSORS
					{
						BasicBlock* pred = *j;
						std::vector<BasicBlock*>::iterator test;
						test=find(loop.begin(),loop.end(),pred);
						if(test==loop.end())	//Not Found
						{
							loop.push_back(pred);
							stack.push_back(pred);
							//errs()<<"Node "<<pred->getName()<<" is pushed into loop.\n";
							LoopSet[EdgeKey].push_back(pred->getName().str());
						}
						
					}
					
				}
				//Print Loop
				errs()<<"\nLoop: ";
				for(auto l=loop.begin();l<loop.end();l++)
				{
					if(l!=loop.begin()) errs()<<" ";
					errs()<<(*l)->getName();
				}


			}

			//Process Basic Blocks
			for(auto &BB: F) {

				runOnBasicBlock(BB);
				// Add the footer to Main's BB containing the return 0
				if(isa<ReturnInst>(BB.getTerminator())) { 
				addFinalUpdates(BB, Context, printf_func);
				}
				
				//for(auto &I: BB)	errs() << I << "\n";	//Print LLVM Instructions
			}

			//End
			errs()<<"\n*************************\n";
			 
			return true; // since runOnBasicBlock has modified the program
		}
		 
		//----------------------------------
			bool runOnBasicBlock(BasicBlock &BB) {
			//CAKE: Get index
				std::string theIndex=(BB.getName().str().substr(5));
				if(theIndex.length()==0) theIndex="0";
				int tmp=stoi(theIndex);

			//CAKE: Write the predecessors
			errs() << "\nBasicBlock: \n" << BB.getName() << ":\t\t\t; Preds: ";	
			for( auto i = pred_begin(&BB); i != pred_end(&BB);i++)	
			{
			BasicBlock* pred = *i;
				errs()<<pred->getName()<<" ";
			}
			errs()<<"\n";
			
			//CAKE: Count Basic Blocks
			IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction

			Value *loadAddr = IRB.CreateLoad(Counters[BB.getName()]);
			Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
			IRB.CreateStore(addAddr, Counters[BB.getName()]);


			//CAKE: Count Edges
			//Create the dynamic index with lastIndex and currentIndex, increment the space and finally, set currentIndex the same as lastIndex.
			 
			//Insert edge adding mechanism in the end of every block 
			IRBuilder<> IRB2(BB.getTerminator());
			IRB2.CreateStore(ConstantInt::get(Type::getInt32Ty(*Context), tmp), currentIndex);

			Value* tmpL0=IRB2.CreateLoad(lastIndex);
			Value* tmpM=IRB2.CreateMul(tmpL0,ConstantInt::get(Type::getInt32Ty(*Context), nodeNum));//last*N
			Value* tmpL1=IRB2.CreateLoad(currentIndex);
			Value* tmpA=IRB2.CreateAdd(tmpM,tmpL1);//last*N+current
			
			Value* tmpEdgePtr = IRB2.CreateGEP(EdgeFreqArray, tmpA);
			Value* loadInc=IRB2.CreateLoad(tmpEdgePtr);
			Value* addInc=IRB2.CreateAdd(loadInc,ConstantInt::get(Type::getInt32Ty(*Context), 1));
			IRB2.CreateStore(addInc, tmpEdgePtr);

			IRB2.CreateStore(ConstantInt::get(Type::getInt32Ty(*Context), tmp), lastIndex);	//CAKE: Set "lastIndex" to the number of the basic block


			return true;
		}
		 
		//----------------------------------
		// Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
		// For this, prepare the SCCGraph, and append to last BB?
		void addFinalUpdates(BasicBlock& BB, LLVMContext *Context, Function *printf_func) 
		{
			IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
			
			std::vector<Constant*> indices;
			Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
			indices.push_back(zero);
			indices.push_back(zero);
			
			Constant *var_ref = ConstantExpr::getGetElementPtr(BasicBlockPrintfFormatStr, indices);
			Constant *var_ref2 = ConstantExpr::getGetElementPtr(BasicBlockPrintfFormatStr2, indices);
			
			Value* GeneralPrintStr;
			CallInst* call;
			Value* bbc;
			//CAKE: Intro
			std::string introStr="********************************\nAfter finishing "+BB.getParent()->getName().str()+"():\n********************************";
			
			GeneralPrintStr=builder.CreateGlobalString(introStr);	//Constant input (such as "This is a test") also acceptable!
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
			
			
			
			//CAKE: Print Block Count
			GeneralPrintStr=builder.CreateGlobalString("\nNode frequency:\n");	//Constant input (such as "This is a test") also acceptable!
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
				
			for(std::map<std::string,GlobalVariable*>::iterator i=Counters.begin();i!=Counters.end();i++)
			{
				
				GeneralPrintStr=builder.CreateGlobalString((i->first));	
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
				
				bbc = builder.CreateLoad(Counters[i->first]);	//
				call = builder.CreateCall2(printf_func, var_ref2, bbc);	
				call->setTailCall(false);
			}
			//CAKE: Print Edge Count
			GeneralPrintStr=builder.CreateGlobalString("\nEdge frequency:\n");	//Constant input (such as "This is a test") also acceptable!
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
			//

			
			for(std::map<std::string,GlobalVariable*>::iterator i=EdgeCounters.begin();i!=EdgeCounters.end();i++)
			{
				std::string str=i->first;
				str.insert(str.find('B',1),"->");
				
				GeneralPrintStr=builder.CreateGlobalString(str);
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
				//Find edges in the array
				std::string headNode=(str.substr(str.find('K',1)+1,str.find('-',1)-str.find('K',1)-1));
				std::string tailNode=(str.substr(str.find('>',1)+6));
				if(headNode.length()==0) headNode="0";
				if(tailNode.length()==0) tailNode="0";
				
				int headNodeInt=stoi(headNode);
				int tailNodeInt=stoi(tailNode);
				
		//		errs()<<headNodeInt<<" AND "<<tailNodeInt<<" IS CAKE! \n";
				
				int K=headNodeInt*nodeNum+tailNodeInt;
				
				Value* iter = builder.CreateGEP(EdgeFreqArray, ConstantInt::get(IntegerType::get(getGlobalContext(), 32), K));
				//
				std::string EdgeName="BLOCK";
				EdgeName+=std::to_string(headNodeInt)+"BLOCK"+std::to_string(tailNodeInt);
				bbc=builder.CreateLoad(iter);	
				Value* cnn=builder.CreateLoad(EdgeCounters[EdgeName]);	
				Value* edgeFinal=builder.CreateAdd(cnn,bbc);
				builder.CreateStore(edgeFinal, EdgeCounters[EdgeName]);
				
				call = builder.CreateCall2(printf_func,var_ref2 , edgeFinal);	
				call->setTailCall(false);

			}
			//CAKE: Print Loop Count
			GeneralPrintStr=builder.CreateGlobalString("\nLoop frequency:\n");	
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
			for(auto i=backEdgesSet.begin();i!=backEdgesSet.end();i+=2)
			{			
				std::string BackEdgeName=(*i)->getName().str()+(*(i+1))->getName().str();
				std::string str;
				for(auto j=LoopSet[BackEdgeName].begin();j!=LoopSet[BackEdgeName].end();j++)
				{
					if(j!=LoopSet[BackEdgeName].begin()) str+="-";
					str+=(*j);
				}
				
				GeneralPrintStr=builder.CreateGlobalString(str);	
				call = builder.CreateCall2(printf_func, var_ref, GeneralPrintStr);	
				call->setTailCall(false);
				
				bbc=builder.CreateLoad(EdgeCounters[BackEdgeName]);	
				call = builder.CreateCall2(printf_func,var_ref2 , bbc);	
				call->setTailCall(false);
				
			}

		}
	};
}
 
char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);

