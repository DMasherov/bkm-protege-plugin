package mpei.bkm.protegeplugin.menu;

import mpei.bkm.converters.UnconvertableException;
import mpei.bkm.converters.text2scheme.Text2SchemeContainerConverter;
import mpei.bkm.model.lss.Attribute;
import mpei.bkm.model.lss.datatypespecification.datatypes.*;
import mpei.bkm.model.lss.objectspecification.concept.BKMClass;
import mpei.bkm.model.lss.objectspecification.concept.BinaryLink;
import mpei.bkm.model.lss.objectspecification.concept.Concept;
import mpei.bkm.model.lss.objectspecification.concepttypes.BKMClassType;
import mpei.bkm.model.lss.objectspecification.concepttypes.ConceptType;
import mpei.bkm.model.lss.objectspecification.concepttypes.StarConceptType;
import mpei.bkm.model.lss.objectspecification.concepttypes.UnionConceptType;
import mpei.bkm.model.lss.objectspecification.intervalrestrictions.AtomRestriction;
import mpei.bkm.model.lss.objectspecification.intervalrestrictions.number.*;
import mpei.bkm.parsing.structurescheme.SchemeContainer;
import org.protege.editor.core.ui.util.UIUtil;
import org.protege.editor.owl.OWLEditorKit;
import org.protege.editor.owl.model.event.EventType;
import org.protege.editor.owl.ui.action.ProtegeOWLAction;
import org.semanticweb.owlapi.model.*;
import uk.ac.manchester.cs.owl.owlapi.*;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;

public class BKMMenu extends ProtegeOWLAction {
    private static final long serialVersionUID = 2452385628012488946L;

    private OWLEditorKit editorKit;

    public void initialise() throws Exception {
        editorKit = getOWLEditorKit();
    }

    public void dispose() throws Exception {
    }

    static Map<PrimitiveDataType.PRIMITIVEDATATYPE,IRI> bkmPrimitiveMap = new HashMap<PrimitiveDataType.PRIMITIVEDATATYPE, IRI>();
    static {
        bkmPrimitiveMap.put(PrimitiveDataType.PRIMITIVEDATATYPE.String,IRI.create("http://www.w3.org/2001/XMLSchema#string"));
        bkmPrimitiveMap.put(PrimitiveDataType.PRIMITIVEDATATYPE.Integer,IRI.create("http://www.w3.org/2001/XMLSchema#integer"));
        bkmPrimitiveMap.put(PrimitiveDataType.PRIMITIVEDATATYPE.Boolean,IRI.create("http://www.w3.org/2001/XMLSchema#boolean"));
        bkmPrimitiveMap.put(PrimitiveDataType.PRIMITIVEDATATYPE.Number,IRI.create("http://www.w3.org/2001/XMLSchema#float"));
        bkmPrimitiveMap.put(PrimitiveDataType.PRIMITIVEDATATYPE.Char,IRI.create("http://www.w3.org/2001/XMLSchema#string"));
    }

    public void loadIntoOntology(OWLOntology owlOntology, SchemeContainer schemeContainer) {
        List<OWLClass> owlClassList = new ArrayList<OWLClass>();
        List<OWLAxiom> owlAxioms = new ArrayList<OWLAxiom>();
        Map<OWLObjectProperty,String> classRangesToAdd = new HashMap<OWLObjectProperty, String>();
        Map<OWLObjectProperty,List<String>> unionClasses = new HashMap<OWLObjectProperty, List<String>>();
        Map<String, OWLClass> nameClassMapping = new HashMap<String, OWLClass>();
        Map<OWLClass, List> exactRestrictions = new HashMap<OWLClass,List>();
        Set<List> linkIntervalRestrictions = new HashSet<List>();
        for (Concept concept : schemeContainer.getScheme().getConceptSet()) {
            OWLClass owlClass = new OWLClassImpl(IRI.create("#" + concept.getName()));
            nameClassMapping.put(concept.getName(), owlClass);
            owlAxioms.add(new OWLDeclarationAxiomImpl(
                    owlClass,Collections.EMPTY_SET
            ));
            owlClassList.add(owlClass);
            exactRestrictions.put(owlClass, new ArrayList());
            if (concept instanceof BinaryLink) {
                BinaryLink link = (BinaryLink)concept;
                String leftName = link.getLeft().getConceptAttribute().getName();
                OWLObjectProperty left = new OWLObjectPropertyImpl(
                        IRI.create("#" + link.getName() + "_" + leftName)
                );
                linkIntervalRestrictions.add(Arrays.asList(owlClass, left, link.getRestriction().getLeft(), leftName));
                owlAxioms.add(new OWLDeclarationAxiomImpl(left,Collections.EMPTY_SET));
                String rightName = link.getRight().getConceptAttribute().getName();
                OWLObjectProperty right = new OWLObjectPropertyImpl(
                        IRI.create("#" + link.getName() + "_" + rightName)
                );
                owlAxioms.add(new OWLDeclarationAxiomImpl(right, Collections.EMPTY_SET));
                owlAxioms.add(new OWLObjectPropertyDomainAxiomImpl(
                        left,
                        owlClass,
                        Collections.EMPTY_SET));
                owlAxioms.add(new OWLObjectPropertyDomainAxiomImpl(
                        right,
                        owlClass,
                        Collections.EMPTY_SET));
                linkIntervalRestrictions.add(Arrays.asList(owlClass, right, link.getRestriction().getRight(), rightName));
            }
            for (Attribute attribute : concept.getAttributes()) {
                if (attribute.getType() instanceof DataType) {
                    OWLDataProperty owlProperty = new OWLDataPropertyImpl(
                        IRI.create("#" + concept.getName() + "_" + attribute.getName())
                    );
                    owlAxioms.add(new OWLDeclarationAxiomImpl(
                            owlProperty,Collections.EMPTY_SET
                    ));
                    owlAxioms.add(new OWLDataPropertyDomainAxiomImpl(
                            owlProperty,
                            owlClass,
                            Collections.EMPTY_SET));

                    if (attribute.getType() instanceof PrimitiveDataType) {
                        PrimitiveDataType.PRIMITIVEDATATYPE t = ((PrimitiveDataType) attribute.getType()).getType();

                        OWLDatatype type = new OWLDatatypeImpl(bkmPrimitiveMap.get(t));
                        owlAxioms.add(new OWLDataPropertyRangeAxiomImpl(
                                owlProperty,
                                type,
                                Collections.EMPTY_SET));

                        exactRestrictions.get(owlClass).addAll(Arrays.asList(owlProperty, type));
                    }
                    if (attribute.getType() instanceof StarDataType &&
                            ((StarDataType) attribute.getType()).getType() instanceof PrimitiveDataType) {
                        PrimitiveDataType.PRIMITIVEDATATYPE t = ((PrimitiveDataType)((StarDataType) attribute.getType()).getType()).getType();

                        OWLDatatype type = new OWLDatatypeImpl(bkmPrimitiveMap.get(t));
                        owlAxioms.add(new OWLDataPropertyRangeAxiomImpl(
                                owlProperty,
                                type,
                                Collections.EMPTY_SET));
                    }
                    if (attribute.getType() instanceof EnumType) {
                        Set<OWLLiteral> enums = new HashSet<OWLLiteral>();
                        OWLDatatype stringType = new OWLDatatypeImpl(bkmPrimitiveMap.get(PrimitiveDataType.PRIMITIVEDATATYPE.String));
                        for (String value : ((EnumType) attribute.getType()).getValues()) {
                            enums.add(new OWLLiteralImpl(value,null,stringType));
                        }
                        owlAxioms.add(new OWLDataPropertyRangeAxiomImpl(
                                owlProperty,
                                new OWLDataOneOfImpl(enums),
                                Collections.EMPTY_SET));
                    }
                    if (attribute.getType() instanceof UnionDataType) {
                        DataType leftDataType = ((UnionDataType) attribute.getType()).getLeft();
                        DataType rightDataType = ((UnionDataType) attribute.getType()).getRight();
                        if (leftDataType instanceof PrimitiveDataType && rightDataType instanceof PrimitiveDataType) {
                            PrimitiveDataType.PRIMITIVEDATATYPE left = ((PrimitiveDataType) leftDataType).getType();
                            PrimitiveDataType.PRIMITIVEDATATYPE right = ((PrimitiveDataType) rightDataType).getType();

                            OWLDataUnionOf owlDataUnionOf = new OWLDataUnionOfImpl(
                                    new HashSet<OWLDataRange>(Arrays.asList(
                                            new OWLDatatypeImpl(bkmPrimitiveMap.get(left)),
                                            new OWLDatatypeImpl(bkmPrimitiveMap.get(right)))
                                    ));
                            owlAxioms.add(new OWLDataPropertyRangeAxiomImpl(
                                    owlProperty,
                                    owlDataUnionOf,
                                    Collections.EMPTY_SET));
                        }
                    }
                }
                if (attribute.getType() instanceof ConceptType) {
                    OWLObjectProperty owlProperty = new OWLObjectPropertyImpl(
                            IRI.create("#" + concept.getName() + "_" + attribute.getName())
                    );
                    owlAxioms.add(new OWLDeclarationAxiomImpl(
                            owlProperty, Collections.EMPTY_SET
                    ));
                    owlAxioms.add(new OWLObjectPropertyDomainAxiomImpl(
                            owlProperty,
                            owlClass,
                            Collections.EMPTY_SET));
                    if (attribute.getType() instanceof BKMClassType) {
                        classRangesToAdd.put(owlProperty, ((BKMClassType) attribute.getType()).getBKMClass().getName());
                        exactRestrictions.get(owlClass).addAll(Arrays.asList(owlProperty, ((BKMClassType) attribute.getType()).getBKMClass().getName()));
                    }
                    if (attribute.getType() instanceof StarConceptType &&
                            ((StarConceptType)attribute.getType()).getType() instanceof BKMClassType) {
                        classRangesToAdd.put(owlProperty, ((BKMClassType) ((StarConceptType) attribute.getType()).getType()).getBKMClass().getName());
                    }
                    if (attribute.getType() instanceof UnionConceptType) {
                        ConceptType leftConceptType = ((UnionConceptType) attribute.getType()).getLeft();
                        ConceptType rightConceptType = ((UnionConceptType) attribute.getType()).getRight();
                        if (leftConceptType instanceof BKMClassType && rightConceptType instanceof BKMClassType) {
                            unionClasses.put(owlProperty, Arrays.asList(
                                            ((BKMClassType) leftConceptType).getBKMClass().getName(),
                                            ((BKMClassType) rightConceptType).getBKMClass().getName())
                            );
                        }
                    }
                }
            }
        }
        owlAxioms.add(new OWLDisjointClassesAxiomImpl(new HashSet<OWLClassExpression>(owlClassList),Collections.EMPTY_SET));
        for (BKMClass bkmClass : schemeContainer.getCollections().allDeclaredBKMClasses) {
            OWLClass subOwlClass = nameClassMapping.get(bkmClass);
            if (bkmClass.getIsa() != null) {
                OWLClass superOwlClass = nameClassMapping.get(bkmClass.getIsa().getName());
                owlAxioms.add(new OWLSubClassOfAxiomImpl(subOwlClass,superOwlClass,Collections.EMPTY_SET));
            }
        }
        for (Map.Entry<OWLObjectProperty, String> e : classRangesToAdd.entrySet()) {
            OWLClass owlClass = nameClassMapping.get(e.getValue());
            if (owlClass != null && owlClass.getIRI().getFragment().equals(e.getValue())) {
                owlAxioms.add(new OWLObjectPropertyRangeAxiomImpl(
                        e.getKey(),
                        owlClass,
                        Collections.EMPTY_SET));
            }
        }
        E: for(Map.Entry<OWLClass,List> e: exactRestrictions.entrySet()) {
            if (e.getValue().size() < 2) {
                continue;
            }
            Set<OWLClassExpression> equiProps = new HashSet<OWLClassExpression>();
            equiProps.add(e.getKey());
            Set<OWLClassExpression> propertyCardinalities = new HashSet<OWLClassExpression>();
            for (int i = 0; i <= (e.getValue()).size() / 2; i+=2) {
                // i: property
                // i + 1:class name
                if (e.getValue().get(i+1) instanceof String) {
                    OWLObjectProperty ope = (OWLObjectProperty) e.getValue().get(i);
                    OWLClass owlClass = nameClassMapping.get(e.getValue().get(i+1));
                    if (owlClass == null) {
                        continue E;
                    }
                    propertyCardinalities.add(new OWLObjectExactCardinalityImpl(ope, 1, owlClass));
                }
                else {
                    OWLDataProperty ope = (OWLDataProperty) e.getValue().get(i);
                    OWLDatatype type = (OWLDatatype) e.getValue().get(i + 1);
                    propertyCardinalities.add(new OWLDataExactCardinalityImpl(ope, 1, type));
                }
            }
            equiProps.add(new OWLObjectIntersectionOfImpl(propertyCardinalities));
            owlAxioms.add(new OWLEquivalentClassesAxiomImpl(equiProps, Collections.EMPTY_SET));
        }
        for(List e: linkIntervalRestrictions) {
            if (e.size() < 4)
                continue;
            // 0: owl class (BKM link)
            // 1: property
            // 2: BKM Interval restriction
            // 3: class name
            Set<OWLClassExpression> equiProps = new HashSet<OWLClassExpression>();
            equiProps.add((OWLClassExpression) e.get(0));
            Set<OWLClassExpression> propertyCardinalities = new HashSet<OWLClassExpression>();
            OWLObjectProperty ope = (OWLObjectProperty) e.get(1);
            OWLClass owlClass = nameClassMapping.get(e.get(3));
            if (owlClass == null)
                continue;
            AtomRestriction atomRestriction = (AtomRestriction) e.get(2);
            Integer min = null, max = null;
            if (atomRestriction instanceof IntervalAtomRestriction) {
                min = ((IntervalAtomRestriction)atomRestriction).getFrom();
                max = ((IntervalAtomRestriction)atomRestriction).getTo();
            }
            else if (atomRestriction instanceof GTAtomRestriction) {
                min = ((GTAtomRestriction)atomRestriction).getValue() + 1;
            }
            else if (atomRestriction instanceof GEAtomRestriction) {
                min = ((GEAtomRestriction)atomRestriction).getValue();
            }
            else if (atomRestriction instanceof LTAtomRestriction) {
                max = ((LTAtomRestriction)atomRestriction).getValue() - 1;
            }
            else if (atomRestriction instanceof LEAtomRestriction) {
                max = ((LEAtomRestriction)atomRestriction).getValue();
            }
            else if (atomRestriction instanceof EQAtomRestriction) {
                Integer exact = ((EQAtomRestriction)atomRestriction).getValue();
                propertyCardinalities.add(new OWLObjectExactCardinalityImpl(ope, exact, owlClass));
            }
            if (min != null) {
                propertyCardinalities.add(new OWLObjectMinCardinalityImpl(ope, min, owlClass));
            }
            if (max != null) {
                propertyCardinalities.add(new OWLObjectMaxCardinalityImpl(ope, max, owlClass));
            }
            if (propertyCardinalities.size() > 0) {
                equiProps.addAll(propertyCardinalities);
                owlAxioms.add(new OWLEquivalentClassesAxiomImpl(equiProps, Collections.EMPTY_SET));
            }
        }
        U: for (Map.Entry<OWLObjectProperty, List<String>> e : unionClasses.entrySet()) {
            Set<OWLClass> unionOfOWLClasses = new HashSet<OWLClass>();
            for (String bkmClassName : e.getValue()) {
                OWLClass owlClass = nameClassMapping.get(bkmClassName);
                if (owlClass == null)
                    continue U;
                unionOfOWLClasses.add(owlClass);
            }
            OWLObjectUnionOf owlObjectUnionOf = new OWLObjectUnionOfImpl(unionOfOWLClasses);
            owlAxioms.add(new OWLObjectPropertyRangeAxiomImpl(
                    (OWLObjectPropertyExpression) e.getKey(),
                    owlObjectUnionOf,
                    Collections.EMPTY_SET
            ));
        }
        for (OWLAxiom owlAxiom : owlAxioms) {
            getOWLModelManager().applyChange(new AddAxiom(owlOntology,owlAxiom));
        }
        getOWLModelManager().fireEvent(EventType.ONTOLOGY_CREATED);
        getOWLModelManager().fireEvent(EventType.ACTIVE_ONTOLOGY_CHANGED);
    }
    public void actionPerformed(ActionEvent arg0) {
        try {
            //getOWLModelManager().setLoadErrorHandler();
            File file = UIUtil.openFile(new JDialog(), "Open BKM file", "Open BKM file", new HashSet<String>(Arrays.asList("bkm")));
            if (file != null) {
                try {
                   translateBKMFile(file);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        } catch (Exception e) {
        }
    }

    private String join(CharSequence seq, List<String> list) {
        StringBuffer sb = new StringBuffer();
        boolean first = false;
        for (String s : list) {
            if (!first) {
                sb.append(seq);
                first = true;
            }
            sb.append(s);
        }
        return sb.toString();
    }
    private void translateBKMFile(File file) {
        BufferedReader br = null;
        try {
            br = new BufferedReader(new FileReader(file));
            String line;
            StringBuffer sb = new StringBuffer();
            while ((line = br.readLine()) != null) {
                sb.append(line).append('\n');
            }
            Text2SchemeContainerConverter converter = new Text2SchemeContainerConverter();

            SchemeContainer schemeContainer = converter.convert(sb.toString());
            String errors = null;
            String incompleteness = null;
            if (converter.getErrors().size() > 0) {
                errors = "Found errors:\n" + join("\n", converter.getErrors());
            }
            if (converter.getIncompleteness().size() > 0) {
                incompleteness = "Found incompleteness:\n" + join("\n", converter.getIncompleteness());
            }
            if (errors != null || incompleteness != null) {
                if (errors == null) {
                    errors = incompleteness;
                }
                else if (incompleteness != null) {
                    errors += "\n" + incompleteness;
                }
                errors += "\nTry to convert to OWL anyway?";
                String[] options = {"Yes", "No"};
                int continueAnswer = JOptionPane.showOptionDialog(new JDialog(), errors, "Errors and incompleteness",
                        JOptionPane.YES_NO_OPTION,
                        JOptionPane.WARNING_MESSAGE,
                        null,
                        options,
                        options[1]
                );
                if (continueAnswer == JOptionPane.NO_OPTION) {
                    return;
                }
            }
            IRI filiIRI = IRI.create(("http://www.mpei.ru/BKM/" +
                    System.getProperty("user.name") + "/" +
                    schemeContainer.getScheme().getName()).replace(" ", "_"));
            OWLOntologyID bkm2OWLOntologyID = new OWLOntologyID(filiIRI);
            for (OWLOntology owlOntology : getOWLModelManager().getOntologies()) {
                if (bkm2OWLOntologyID.equals(owlOntology.getOntologyID())) {
                    getOWLModelManager().removeOntology(owlOntology);
                }
            }
            OWLOntology owlOntology = getOWLModelManager().createNewOntology(
                    bkm2OWLOntologyID,
                    filiIRI.toURI());

            loadIntoOntology(owlOntology, schemeContainer);
        } catch (IOException e) {
            JOptionPane.showMessageDialog(new JDialog(), e.getMessage(), "Error when reading BKM file.", JOptionPane.ERROR_MESSAGE);
        } catch (UnconvertableException e) {
            JOptionPane.showMessageDialog(new JDialog(), e.getMessage(), "Error when translating BKM file.", JOptionPane.ERROR_MESSAGE);
        } catch (OWLOntologyCreationException e) {
            JOptionPane.showMessageDialog(new JDialog(), e.getMessage(), "Error when creating OWL ontology from BKM file.", JOptionPane.ERROR_MESSAGE);
        } catch (Exception e) {
            JOptionPane.showMessageDialog(new JDialog(), "Unknown error when reading BKM file.", "Error when reading BKM file.", JOptionPane.ERROR_MESSAGE);
        }

        /*
        final OWLOntology currentOntology = getOWLModelManager().getActiveOntology();
        final OWLWorkspace editorWindow = editorKit.getOWLWorkspace();
        JDialog cellfieDialog = WorkspacePanel.createDialog(currentOntology, workbookPath, editorKit, dialogManager);
        cellfieDialog.setLocationRelativeTo(editorWindow);
        cellfieDialog.setVisible(true);
        */
    }
}

