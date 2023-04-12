package org.renaissance.json;

import java.time.LocalDate;
import java.util.Random;

class EmployeeGenerator {
    private static final long DatesFrom = LocalDate.of(1950, 1, 1).toEpochDay();
    private static final long DatesTo = LocalDate.of(2020, 1, 1).toEpochDay();
    private static final String[] FirstNames = { "Anna", "Bob", "Cecille", "Dunno", "Emma", "Frantisek" };
    private static final String[] LastNames = { "Smith", "Johnson", "Williams", "Brown", "Jones" };
    private static final String[] CarVendors = { "Audi", "BMW", "Tesla", "Lada" };
    private static final String CodeChars = "abcdefghijklmnopqrstuvwxyz0123456789";

    private final Random random;

    public EmployeeGenerator(long seed) {
        random = new Random(seed);
    }

    public Employee createEmployee(int width, int depthRemaining) {
        final Employee emp = new Employee();

        emp.setBirthday(randomDate());
        emp.setDepartment(Employee.Department.REASEARCH);
        emp.setFirstName(randomItem(FirstNames));
        emp.setLastName(randomItem(LastNames));
        emp.setSalary(random.nextInt(10000, 100000));
        emp.setRating(random.nextDouble(-100.0, 100.0));

        if (random.nextBoolean()) {
            final Asset.Computer computer = new Asset.Computer(random.nextLong());
            computer.setRam(random.nextInt(1, 128));
            computer.setCores(random.nextInt(1, 64));
            computer.setPassword(randomCode(10));
            emp.getAssets().add(computer);
        }

        if (random.nextBoolean()) {
            final Asset.Car car = new Asset.Car(random.nextLong());
            car.setColor(randomCode(4));
            car.setVendor(randomItem(CarVendors));
            car.setProductionDate(randomDate());
            emp.getAssets().add(car);
        }

        if (depthRemaining > 0) {
            for (int i = 0; i < width; i++) {
                final Employee subordinate = createEmployee(width, depthRemaining - 1);
                emp.getSubordinates().add(subordinate);
            }
        }

        return emp;
    }

    private <T> T randomItem(T[] array) {
        return array[random.nextInt(array.length)];
    }

    private LocalDate randomDate() {
        long epochDay = random.nextLong(DatesFrom, DatesTo);
        return LocalDate.ofEpochDay(epochDay);
    }

    private String randomCode(int length) {
        StringBuilder sb = new StringBuilder(length);
        for (int i = 0; i < length; i++) {
            sb.append(CodeChars.charAt(random.nextInt(CodeChars.length())));
        }
        return sb.toString();
    }
}
