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

import edu.kit.joana.api.sdg.SDGConfig;
import edu.kit.joana.api.sdg.SDGProgram;
import edu.kit.joana.api.sdg.SDGProgramPart;
import edu.kit.joana.ifc.sdg.graph.SDG;
import edu.kit.joana.ifc.sdg.graph.SDGNode;
import edu.kit.joana.ifc.sdg.graph.SDGNodeTuple;
import edu.kit.joana.ifc.sdg.graph.slicer.SDGSlicer;
import edu.kit.joana.ifc.sdg.graph.slicer.conc.CFGBackward;
import edu.kit.joana.ifc.sdg.mhpoptimization.MHPType;
import edu.kit.joana.ifc.sdg.util.JavaMethodSignature;
import edu.kit.joana.util.Stubs;
import edu.kit.joana.wala.core.SDGBuilder.ExceptionAnalysis;
import edu.kit.joana.wala.core.SDGBuilder.PointsToPrecision;

public class SlicerTest {

	public static void main(String[] args) {
//		ClassPathParser parser = new ClassPathParser();
//		parser.parseSystemClasspath();
//		parser.addElementToClassPath(new File("HelloWorld.jar"));
		
		
		
//		CommandLine.parse(args);
//		try {
//			doSlicing(Paths.get("HelloWorld.jar").toAbsolutePath().toString());
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (CancelException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (ClassHierarchyException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (IllegalArgumentException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (WalaException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		
		
		try {
			doSlicingNew(Paths.get("HelloWorld2.jar").toAbsolutePath().toString());
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
		} catch (UnsoundGraphException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public static void doSlicingNew(String appJar) throws UnsoundGraphException, ClassHierarchyException, IOException, CancelException {
		/** the class path is either a directory or a jar containing all the classes of the program which you want to analyze */
		String classPath = appJar;
		
		/** the entry method is the main method which starts the program you want to analyze */
		JavaMethodSignature entryMethod = JavaMethodSignature.mainMethodOfClass("HelloWorld.HelloWorld");
		
		/** For multi-threaded programs, it is currently neccessary to use the jdk 1.4 stubs */
		SDGConfig config = new SDGConfig(classPath, entryMethod.toBCString(), Stubs.JRE_14);
		
		/** compute interference edges to model dependencies between threads (set to false if your program does not use threads) */
		config.setComputeInterferences(false);
		
		/** additional MHP analysis to prune interference edges (does not matter for programs without multiple threads) */
		config.setMhpType(MHPType.PRECISE);
		
		/** precision of the used points-to analysis - INSTANCE_BASED is a good value for simple examples */
		config.setPointsToPrecision(PointsToPrecision.INSTANCE_BASED);
		
		/** exception analysis is used to detect exceptional control-flow which cannot happen */
		config.setExceptionAnalysis(ExceptionAnalysis.INTERPROC);
		
		/** build the PDG */
		SDGProgram program = SDGProgram.createSDGProgram(config, System.out, new NullProgressMonitor());
		
//		/** optional: save PDG to disk */
//		SDGSerializer.toPDGFormat(program.getSDG(), new FileOutputStream("yourSDGFile.pdg"));
		
//		IFCAnalysis ana = new IFCAnalysis(program);
//		/** annotate sources and sinks */
//		// for example: fields
//		ana.addSourceAnnotation(program.getPart("HelloWorld.HelloWorld.x"), BuiltinLattices.STD_SECLEVEL_HIGH);
//		ana.addSinkAnnotation(program.getPart("HelloWorld.HelloWorld.y"), BuiltinLattices.STD_SECLEVEL_LOW);
//		
//		/** run the analysis */
//		Collection<? extends IViolation<SecurityNode>> result = ana.doIFC();
//		TObjectIntMap<IViolation<SDGProgramPart>> resultByProgramPart = ana.groupByPPPart(result);
//		/** do something with result */
//		for (IViolation<SDGProgramPart> vio : resultByProgramPart.keySet()) {
//			System.out.println(vio);
//		}

		List<SDGNodeTuple> allCallSites = program.getSDG()
				.getAllCallSites();
		for (SDGNodeTuple sdgNodeTuple : allCallSites) {
			System.out.println("primeiro: "
					+ sdgNodeTuple.getFirstNode().getBytecodeName() + " " + sdgNodeTuple.getFirstNode().getEr()
					+ " segundo: "
					+ sdgNodeTuple.getSecondNode().getBytecodeName() + " " + + sdgNodeTuple.getSecondNode().getEr());
		}

		System.out.println(program.getMethodParameter(JavaMethodSignature.fromString("java.io.PrintStream.println(Ljava/lang/String;)V"),0));
//		System.out.println(program.getClasses());
		System.out.println(program.getAllMethods());
		System.out.println(program.getAllProgramParts());
		System.out.println(program.getCallsToMethod(JavaMethodSignature.fromString("java.io.PrintStream.println(Ljava/lang/String;)V")));
		SDG g = program.getSDG();
		SDGNode c = g.getNode(36);
//		System.out.println(g.toString());
		Slicer slicer = new Slicer();
		Collection<SDGNode> slice = new CFGBackward(g).slice(c);
		System.out.println(slice);
		for (SDGNode node : slice) {
			System.out.println("* " + node.getBytecodeName());
		}
		System.out.println(new SDGSlicer(g, Collections.singleton(c)).slice());
		
		
		Collection<SDGProgramPart> parts = program.getAllProgramParts();
		for (SDGProgramPart part : parts) {
			System.out.println("+ " + part.toString());
		}
		
		
//		// find seed statement
//		Statement statement = findCallTo(findMainMethod(cg), "println");
//
//		Collection<Statement> slice;
//
//		// context-sensitive traditional slice
//		slice = Slicer.computeBackwardSlice ( statement, cg, pa );
//		dumpSlice(slice);
//
//		// context-sensitive thin slice
//		slice = Slicer.computeBackwardSlice(statement, cg, pa, DataDependenceOptions.NO_BASE_PTRS,
//				ControlDependenceOptions.NONE);
//		dumpSlice(slice);
//
//		// context-insensitive slice
//		ThinSlicer ts = new ThinSlicer(cg,pa);
//		slice = ts.computeBackwardThinSlice ( statement );
//		dumpSlice(slice);
//		
//		return cgb;
	}
	
	public static CallGraphBuilder<InstanceKey> doSlicing(String appJar) throws WalaException, IOException, IllegalArgumentException, CancelException {
		// create an analysis scope representing the appJar as a J2SE application
		AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, new File("exclusions.txt"));
//		String exclusionFile = p.getProperty("exclusions");
		//		  AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, exclusionFile != null ? new File(exclusionFile)
		/* format:
			java\/awt\/.*
			javax\/swing\/.*
			sun\/awt\/.*
			sun\/swing\/.*
			com\/sun\/.*
			sun\/.*
		 */
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
			System.err.println(s);
		}
	}
	
}
