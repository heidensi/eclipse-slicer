package slicer.test;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import com.ibm.wala.classLoader.ShrikeBTMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCache;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisOptions.ReflectionOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.CallGraphBuilder;
import com.ibm.wala.ipa.callgraph.Entrypoint;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXCFABuilder;
import com.ibm.wala.ipa.callgraph.propagation.cfa.ZeroXInstanceKeys;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.Slicer;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.thin.ThinSlicer;
import com.ibm.wala.model.java.lang.reflect.Array;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.types.Descriptor;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.GraphIntegrity.UnsoundGraphException;
import com.ibm.wala.util.io.CommandLine;
import com.ibm.wala.util.strings.Atom;


public class SlicerTest {

	public static void main(String[] args) {
//		ClassPathParser parser = new ClassPathParser();
//		parser.parseSystemClasspath();
//		parser.addElementToClassPath(new File("HelloWorld.jar"));
		
		
		
		CommandLine.parse(args);
		try {
			doSlicing(Paths.get("HelloWorld.jar").toAbsolutePath().toString());
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (CancelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ClassHierarchyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (WalaException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		

	}

	public static CallGraphBuilder<InstanceKey> doSlicing(String appJar) throws WalaException, IOException, IllegalArgumentException, CancelException {
		// create an analysis scope representing the appJar as a J2SE application
//		ClassLoader cl = ClassLoader.getSystemClassLoader();
//		AnalysisScope scope = AnalysisScopeReader.readJavaScope("scope.txt",new File("exclusions.txt") , cl);
		
		AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, new File("exclusions.txt"));
				System.out.println("cha");
		ClassHierarchy cha = ClassHierarchyFactory.make(scope);

		System.out.println("entrypoints");
		Iterable<Entrypoint> entrypoints = Util.makeMainEntrypoints(scope, cha);
		Entrypoint entrypoint = null;
		for (Entrypoint entry : entrypoints) {
			System.out.println(entry.getMethod().getDeclaringClass().getName());
			if (entry.getMethod().getDeclaringClass().getName().toString().equals("LHelloWorld/HelloWorld")) {
				entrypoint = entry;
				System.err.println("***found***");
			}
		}
		AnalysisOptions options = new AnalysisOptions(scope, Collections.singletonList(entrypoint));
//		options.setReflectionOptions(ReflectionOptions.NONE);
		
		System.out.println("default selectors");
		Util.addDefaultSelectors(options, cha);

		System.out.println("cg");
		// build the call graph
		CallGraphBuilder<InstanceKey> cgb = //Util.makeZeroCFABuilder(options, new AnalysisCacheImpl(), cha, scope);
		ZeroXCFABuilder.make(cha, options, new AnalysisCacheImpl(), null, null,
                ZeroXInstanceKeys.ALLOCATIONS | ZeroXInstanceKeys.CONSTANT_SPECIFIC);
		System.out.println("cg make");
		CallGraph cg = cgb.makeCallGraph(options, null);
		System.out.println("cg pa");
		PointerAnalysis<InstanceKey> pa = cgb.getPointerAnalysis();

		System.out.println("stmt find");
		// find seed statements
		List<CGNode> mainMethods = findMainMethods(cg);
		
		for (CGNode mainNode : mainMethods) {
			Statement statement = findCallTo(mainNode, "println");

			if (statement == null) {
				System.err.println("failed to find call to " + "println" + " in " + mainNode);
				continue;
			}
			Collection<Statement> slice;

			// context-sensitive traditional slice
			slice = Slicer.computeBackwardSlice ( statement, cg, pa );
			dumpSlice(slice);

			//		// context-sensitive thin slice
			//		slice = Slicer.computeBackwardSlice(statement, cg, pa, DataDependenceOptions.NO_BASE_PTRS,
			//				ControlDependenceOptions.NONE);
			//		dumpSlice(slice);

			// context-insensitive slice
//			ThinSlicer ts = new ThinSlicer(cg,pa);
//			slice = ts.computeBackwardThinSlice ( statement );
//			dumpSlice(slice);
		}
		
		return cgb;
	}

	public static List<CGNode> findMainMethods(CallGraph cg) {
		Descriptor d = Descriptor.findOrCreateUTF8("([Ljava/lang/String;)V");
		Atom name = Atom.findOrCreateUnicodeAtom("main");
		List<CGNode> result = new ArrayList<>();
		for (Iterator<? extends CGNode> it = cg.getSuccNodes(cg.getFakeRootNode()); it.hasNext();) {
			CGNode n = it.next();
			if (n.getMethod().getName().equals(name) && n.getMethod().getDescriptor().equals(d)) {
				result.add(n);
			}
		}
		
		if (result.isEmpty()) {
			Assertions.UNREACHABLE("failed to find main() method");
		}
		
		return result;
	}

	public static Statement findCallTo(CGNode n, String methodName) {
		IR ir = n.getIR();
		for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
			SSAInstruction s = it.next();
			if (s instanceof com.ibm.wala.ssa.SSAAbstractInvokeInstruction) {
				com.ibm.wala.ssa.SSAAbstractInvokeInstruction call = (com.ibm.wala.ssa.SSAAbstractInvokeInstruction) s;
				System.out.println(n.toString().substring(0, 20) + " " + call.getCallSite().getDeclaredTarget().getName().toString());
				if (call.getCallSite().getDeclaredTarget().getName().toString().equals(methodName)) {
					com.ibm.wala.util.intset.IntSet indices = ir.getCallInstructionIndices(call.getCallSite());
					com.ibm.wala.util.debug.Assertions.productionAssertion(indices.size() == 1, "expected 1 but got " + indices.size());
					return new com.ibm.wala.ipa.slicer.NormalStatement(n, indices.intIterator().next());
				}
			}
		}
		//Assertions.UNREACHABLE("failed to find call to " + methodName + " in " + n);
		return null;
	}


	public static void dumpSlice(Collection<Statement> slice) {
		for (Statement s : slice) {
//			System.err.println(s);
			if (s.getKind() == Statement.Kind.NORMAL) { // ignore special kinds of statements
				  int bcIndex, instructionIndex = ((NormalStatement) s).getInstructionIndex();
				  try {
				    bcIndex = ((ShrikeBTMethod) s.getNode().getMethod()).getBytecodeIndex(instructionIndex);
				    try {
				      int src_line_number = s.getNode().getMethod().getLineNumber(bcIndex);
				      System.out.print(s.getNode().getMethod().getSignature());
				      System.out.println ( "Source line number = " + src_line_number );
				    } catch (Exception e) {
//				      System.err.println("Bytecode index no good");
//				      System.err.println(e.getMessage());
				    }
				  } catch (Exception e ) {
//				    System.err.println("it's probably not a BT method (e.g. it's a fakeroot method)");
//				    System.err.println(e.getMessage());
				  }
				}
			
		}
	}
	
}
