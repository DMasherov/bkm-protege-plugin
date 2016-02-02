package mpei.bkm.protegeplugin.menu;

import mpei.bkm.converters.UnconvertableException;
import mpei.bkm.converters.text2scheme.Text2SchemeContainerConverter;
import mpei.bkm.model.lss.Attribute;
import mpei.bkm.model.lss.datatypespecification.datatypes.*;
import mpei.bkm.model.lss.objectspecification.concept.BKMClass;
import mpei.bkm.model.lss.objectspecification.concept.Concept;
import mpei.bkm.model.lss.objectspecification.concepttypes.BKMClassType;
import mpei.bkm.model.lss.objectspecification.concepttypes.ConceptType;
import mpei.bkm.model.lss.objectspecification.concepttypes.StarConceptType;
import mpei.bkm.model.structurescheme.Scheme;
import mpei.bkm.parsing.structurescheme.SchemeContainer;
import org.apache.commons.lang.enums.*;
import org.protege.editor.owl.OWLEditorKit;
import org.protege.editor.owl.model.event.EventType;
import org.protege.editor.owl.ui.action.ProtegeOWLAction;
import org.semanticweb.owlapi.model.*;
import uk.ac.manchester.cs.owl.owlapi.*;

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
        Map<String, OWLClass> nameClassMapping = new HashMap<String, OWLClass>();
        Map<OWLClass, List> cardinalities = new HashMap<OWLClass,List>();
        for (Concept concept : schemeContainer.getScheme().getConceptList()) {
            OWLClass owlClass = new OWLClassImpl(IRI.create("#" + concept.getName()));
            nameClassMapping.put(concept.getName(), owlClass);
            owlAxioms.add(new OWLDeclarationAxiomImpl(
                    owlClass,Collections.EMPTY_SET
            ));
            owlClassList.add(owlClass);
            cardinalities.put(owlClass,new ArrayList());
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

                        cardinalities.get(owlClass).addAll(Arrays.asList(owlProperty, type));
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
                        cardinalities.get(owlClass).addAll(Arrays.asList(owlProperty, ((BKMClassType) attribute.getType()).getBKMClass().getName()));
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
            if (owlClass.getIRI().getFragment().equals(e.getValue())) {
                owlAxioms.add(new OWLObjectPropertyRangeAxiomImpl(
                        e.getKey(),
                        owlClass,
                        Collections.EMPTY_SET));
            }
        }
        for(Map.Entry<OWLClass,List> e: cardinalities.entrySet()) {
            Set<OWLClassExpression> equiProps = new HashSet<OWLClassExpression>();
            equiProps.add(e.getKey());
            Set<OWLClassExpression> propertyCardinalities = new HashSet<OWLClassExpression>();
            for (int i = 0; i <= (e.getValue()).size() / 2; i+=2) {
                if (e.getValue().get(i+1) instanceof String) {
                    OWLObjectProperty ope = (OWLObjectProperty) e.getValue().get(i);
                    OWLClass owlClass = nameClassMapping.get(e.getValue().get(i+1));
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
        for (OWLAxiom owlAxiom : owlAxioms) {
            getOWLModelManager().applyChange(new AddAxiom(owlOntology,owlAxiom));
        }
        getOWLModelManager().fireEvent(EventType.ONTOLOGY_CREATED);
        getOWLModelManager().fireEvent(EventType.ACTIVE_ONTOLOGY_CHANGED);
    }
    public void actionPerformed(ActionEvent arg0) {
        try {
            Text2SchemeContainerConverter ttt = new Text2SchemeContainerConverter();

            SchemeContainer schemeContainer = ttt.convert("SCHEME Учебный_процесс:\n" +
                    "    Студент[ФИО:String, ГодРожд:Integer, Группа].\n" +
                    "    Группа[Номер:String, Староста:Студент].\n" +
                    "    Препод[ФИО:String, Должность:String, Стаж:Integer].\n" +
                    "    Предмет[Назв:String, КоличЧасов:Integer,\n" +
                    "            ВидЗанятия:{лекция,семинар,лаб_занятие},\n" +
                    "            Отчет:{экзамен,зачет,зач_и_экз}]. END");

            IRI filiIRI = IRI.create("http://www.mpei.ru/BKM/" +
                    System.getProperty("user.name")+ "/" +
                    schemeContainer.getScheme().getName());
            OWLOntology owlOntology = getOWLModelManager().createNewOntology(
                    new OWLOntologyID(filiIRI),
                    filiIRI.toURI());

            loadIntoOntology(owlOntology, schemeContainer);

            //getOWLModelManager().setLoadErrorHandler();
            /*File file = UIUtil.openFile(new JDialog(), "Open BKM file", s, new HashSet<String>(Arrays.asList("BKM file (.bkmapi)")));
            if (file != null) {
                try {
                    readBKMFile(file);
                } catch (Exception e) {
                    e.printStackTrace();
                }
            }*/
        } catch (Exception e) {
        }
    }

    private void readBKMFile(File file) {
        BufferedReader br = null;
        try {
            br = new BufferedReader(new FileReader(file));
            String line;
            StringBuffer sb = new StringBuffer();
            while ((line = br.readLine()) != null) {
                sb.append(line);
            }
        } catch (IOException e) {
            // TODO logging
            e.printStackTrace();
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

