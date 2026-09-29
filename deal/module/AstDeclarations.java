package deal.module;

import deal.ast.ClassDeclaration;
import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.ProgramNode;
import deal.ast.StatementNode;

/**
 * The shared top-level declaration lookups of the module layer (the
 * planner, recorder, serializer, declaration analyzer, and
 * orchestrator's common walk): a statement's direct-or-exported class/
 * function declaration, the top-level declaration named by a string,
 * and the class behind a synthetic {@code C$fromJson}/{@code C$toJson}
 * export name. Package-local; no resolution, typing, or identity
 * policy lives here.
 */
final class AstDeclarations {

    private AstDeclarations() {
        // Static helpers; no instances.
    }

    /** The class declaration of a top-level statement, direct or exported. */
    static ClassDeclaration classDeclarationOf(StatementNode stmt) {
        if (stmt instanceof ClassDeclaration cd) {
            return cd;
        }
        if (stmt instanceof ExportDeclaration ed
                && ed.declaration() instanceof ClassDeclaration cd) {
            return cd;
        }
        return null;
    }

    /**
     * The function declaration of a top-level statement, direct or
     * exported.
     */
    static FunctionDeclaration functionDeclarationOf(StatementNode stmt) {
        if (stmt instanceof FunctionDeclaration fd) {
            return fd;
        }
        if (stmt instanceof ExportDeclaration ed
                && ed.declaration() instanceof FunctionDeclaration fd) {
            return fd;
        }
        return null;
    }

    /**
     * Finds a top-level function declaration by name (exported
     * declarations included), or null.
     */
    static FunctionDeclaration findFunctionDeclaration(
            ProgramNode program, String name) {
        for (StatementNode stmt : program.statements()) {
            FunctionDeclaration fd = functionDeclarationOf(stmt);
            if (fd != null && fd.name().equals(name)) {
                return fd;
            }
        }
        return null;
    }

    /**
     * Finds a top-level class declaration by name (exported
     * declarations included), or null.
     */
    static ClassDeclaration findClassDeclaration(
            ProgramNode program, String name) {
        for (StatementNode stmt : program.statements()) {
            ClassDeclaration cd = classDeclarationOf(stmt);
            if (cd != null && cd.name().equals(name)) {
                return cd;
            }
        }
        return null;
    }

    /**
     * The class whose synthetic {@code C$fromJson}/{@code C$toJson}
     * export carries the given name, or null.
     */
    static ClassDeclaration jsonableClassForSynthetic(
            ProgramNode program, String name) {
        for (StatementNode stmt : program.statements()) {
            ClassDeclaration cd = classDeclarationOf(stmt);
            if (cd != null && cd.isJsonable()
                    && (name.equals(cd.name() + "$fromJson")
                        || name.equals(cd.name() + "$toJson"))) {
                return cd;
            }
        }
        return null;
    }
}
