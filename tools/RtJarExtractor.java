
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.FileVisitOption;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

public class RtJarExtractor {
    private static void packClassIntoZip(Path classFile, String className, ZipOutputStream zip) throws java.io.IOException {
        ZipEntry classnameEntry = new ZipEntry(className);
        zip.putNextEntry(classnameEntry);
        zip.write(Files.readAllBytes(classFile));
    }

    public static void main(String... args) throws java.io.IOException {
        FileSystem jrtFilesystem = FileSystems.getFileSystem(URI.create("jrt:/"));
        ZipOutputStream rtJar = new ZipOutputStream(Files.newOutputStream(Paths.get(args[0])));

        Files.list(jrtFilesystem.getPath("/modules")).forEach(module -> {
            try {
                Files.walk(module, FileVisitOption.FOLLOW_LINKS).forEach(filename -> {
                    if (!Files.isRegularFile(filename)) {
                        return;
                    }

                    String classname = module.relativize(filename).toString();

                    if (classname.equals("module-info.class")) {
                        return;
                    }

                    try {
                        packClassIntoZip(filename, classname, rtJar);
                    } catch (java.io.IOException e) {
                        throw new RuntimeException(e);
                    }
                });
            } catch (java.io.IOException e) {
                throw new RuntimeException(e);
            }
        });

        rtJar.close();
        jrtFilesystem.close();
    }
}
