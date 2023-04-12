package org.renaissance.json;

import com.fasterxml.jackson.annotation.JsonFormat;

import java.time.LocalDate;
import java.util.ArrayList;

class Employee {
    private String firstName;
    private String lastName;
    private LocalDate birthday;
    private Department department;
    private int salary;
    private double rating;
    private ArrayList<Asset> assets = new ArrayList<>();
    private ArrayList<Employee> subordinates = new ArrayList<>();

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }

        if (!(other instanceof Employee)) {
            return false;
        }

        final Employee otherEmp = (Employee) other;

        return firstName.equals(otherEmp.firstName)
                && lastName.equals(otherEmp.lastName)
                && birthday.equals(otherEmp.birthday)
                && department.equals(otherEmp.department)
                && salary == otherEmp.salary
                && assets.equals(otherEmp.assets)
                && subordinates.equals(otherEmp.subordinates);
    }

    public String getFirstName() {
        return firstName;
    }

    public void setFirstName(String firstName) {
        this.firstName = firstName;
    }

    public String getLastName() {
        return lastName;
    }

    public void setLastName(String lastName) {
        this.lastName = lastName;
    }

    @JsonFormat(shape = JsonFormat.Shape.STRING, pattern = "yyyy-MM-dd")
    public LocalDate getBirthday() {
        return birthday;
    }

    public void setBirthday(LocalDate birthday) {
        this.birthday = birthday;
    }

    public Department getDepartment() {
        return department;
    }

    public void setDepartment(Department department) {
        this.department = department;
    }

    public int getSalary() {
        return salary;
    }

    public void setSalary(int salary) {
        this.salary = salary;
    }

    public double getRating() {
        return rating;
    }

    public void setRating(double rating) {
        this.rating = rating;
    }

    public ArrayList<Asset> getAssets() {
        return assets;
    }

    public void setAssets(ArrayList<Asset> assets) {
        this.assets = assets;
    }

    public ArrayList<Employee> getSubordinates() {
        return subordinates;
    }

    public void setSubordinates(ArrayList<Employee> subordinates) {
        this.subordinates = subordinates;
    }

    enum Department {
        HR,
        PR,
        SALES,
        ACCOUNTING,
        DEVELOPMENT,
        REASEARCH,
        LEGAL,
        SANITATION,
        PHILOSOPHY
    }
}
